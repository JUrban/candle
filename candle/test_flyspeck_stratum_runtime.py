#!/usr/bin/env python3

import copy
import hashlib
import importlib
import json
import os
import py_compile
import signal
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class StratumRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.actions = [
            {
                "index": 0,
                "target": "general/a.hl",
                "source_sha256": "1" * 64,
                "identity_basename": "a.hl",
                "identity_md5": "3" * 32,
            },
            {
                "index": 1,
                "target": "../formal_lp/b.ml",
                "source_sha256": "2" * 64,
                "identity_basename": "b.ml",
                "identity_md5": "4" * 32,
            },
        ]
        self.prefix = (
            b"(* exact leading material *)\n"
            b'#flyspeck_needs "general/a.hl";;\n'
            b"(* retained boundary comment *)\n"
            b'#flyspeck_needs "../formal_lp/b.ml";;\n'
        )
        self.nonce = "a" * 32

    def test_pinned_python_elf_contract_tracks_provenance_schema(self) -> None:
        closure = subject.EXPECTED_PYTHON_RUNTIME["elf_closure"]
        helper = subject.cakeml_artifact_provenance
        self.assertEqual(set(closure), helper.ELF_DYNAMIC_CLOSURE_FIELDS)
        self.assertEqual(closure["policy"], helper.ELF_DYNAMIC_CLOSURE_POLICY)
        helper.validate_elf_closure_record(
            closure, "pinned Python runtime", allowed_dynamic_path_tags={},
        )
        stale = copy.deepcopy(closure)
        stale.pop("dynamic_path_tags")
        with self.assertRaisesRegex(
            helper.ProvenanceError, "malformed pinned Python runtime",
        ):
            helper.validate_elf_closure_record(
                stale, "pinned Python runtime", allowed_dynamic_path_tags={},
            )
    def test_instrumentation_is_ordered_and_output_only(self) -> None:
        result = subject.instrument_prefix(self.prefix, self.actions, self.nonce).decode()
        self.assertIn(self.prefix.splitlines()[0].decode(), result)
        first_action = result.index('#flyspeck_needs "general/a.hl";;')
        first_marker = result.index(subject.ACTION_PREFIX + f" {self.nonce} 000")
        second_action = result.index('#flyspeck_needs "../formal_lp/b.ml";;')
        second_marker = result.index(subject.ACTION_PREFIX + f" {self.nonce} 001")
        self.assertLess(first_action, first_marker)
        self.assertLess(first_marker, second_action)
        self.assertLess(second_action, second_marker)
        self.assertEqual(result.count("candle_flyspeck_stratum_commit_action"), 2)
        self.assertNotIn("print_endline", result)

    def test_instrumentation_rejects_target_drift(self) -> None:
        actions = copy.deepcopy(self.actions)
        actions[1]["target"] = "wrong.ml"
        with self.assertRaisesRegex(subject.ContractError, "directive drift: 1"):
            subject.instrument_prefix(self.prefix, actions, self.nonce)

    def test_log_requires_every_exact_marker_in_order(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            f"{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
        ])
        subject.validate_log(log, self.actions, boundary, self.nonce)

    def test_log_rejects_duplicate_or_late_marker(self) -> None:
        boundary = "00-test-through-001"
        marker0 = f"{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}"
        marker1 = f"{subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}"
        final = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        with self.assertRaisesRegex(subject.ContractError, "duplicate action 0 marker"):
            subject.validate_log(
                "\n".join([preflight, marker0, marker0, marker1, final]),
                self.actions, boundary, self.nonce,
            )
        with self.assertRaisesRegex(subject.ContractError, "out of order"):
            subject.validate_log(
                "\n".join([preflight, marker1, marker0, final]),
                self.actions, boundary, self.nonce,
            )

    def test_log_rejects_top_level_exception(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            f"{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
            "EXCEPTION: injected",
        ])
        with self.assertRaisesRegex(subject.ContractError, "top-level error"):
            subject.validate_log(log, self.actions, boundary, self.nonce)

    def test_quoted_or_prefixed_marker_text_is_not_an_event(self) -> None:
        boundary = "00-test-through-001"
        quoted = "\n".join([
            f'source "{subject.PREFLIGHT_MARKER} {self.nonce}"',
            f'print_endline "{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}";;',
            f'prefix {subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}',
            f'quoted {subject.SUCCESS_MARKER} {self.nonce} {boundary} 2',
        ])
        with self.assertRaisesRegex(subject.ContractError, "stratum preflight marker"):
            subject.validate_log(quoted, self.actions, boundary, self.nonce)

    def test_exact_boundary_fingerprint_requests(self) -> None:
        self.assertEqual(subject.fingerprint_requests("00-base-through-029"), [])
        self.assertEqual(subject.fingerprint_requests("d1-diagnostic-through-018"), [])
        self.assertEqual(
            subject.fingerprint_requests("05-lp_support-through-184"),
            ["Linear_programming_results.linear_programming_results_th"],
        )
        final = subject.fingerprint_requests("07-final_assembly-through-296")
        self.assertEqual(len(final), 4)
        self.assertEqual(final[-1], "Candle_flyspeck_l2.tame_imp_kepler_conjecture")

    def test_candidate_fingerprint_parser_is_fail_closed(self) -> None:
        name = "Linear_programming_results.linear_programming_results_th"
        axioms = b"axioms"
        fields = [
            subject.FINGERPRINT_MARKER,
            name.encode().hex(),
            b"theorem".hex(), subject.reference_protocol.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), axioms.hex(), "0", "3",
        ]
        state = [
            subject.STATE_FINGERPRINT_MARKER,
            b"state".hex(), b"types".hex(), b"terms".hex(),
            b"definitions".hex(), axioms.hex(), "1", "2", "3", "3",
        ]
        serializer = subject.reference_protocol.FINGERPRINT_HELPER
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "fingerprints.log"
            log.write_text(
                "\t".join(fields) + "\n" + "\t".join(state) + "\n",
                encoding="utf-8",
            )
            report = subject.parse_fingerprints(log, [name], serializer)
            self.assertEqual(report["status"], "observed_uncompared")
            self.assertFalse(report["approved_reference_present"])
            self.assertEqual(
                report["theorems"][0]["theorem_sha256"],
                hashlib.sha256(b"theorem").hexdigest(),
            )
            self.assertEqual(
                report["post_state"]["definitions_sha256"],
                hashlib.sha256(b"definitions").hexdigest(),
            )
            bad = fields.copy()
            bad[-1] = "4"
            log.write_text(
                "\t".join(bad) + "\n" + "\t".join(state) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(subject.ContractError, "three axioms"):
                subject.parse_fingerprints(log, [name], serializer)

    def test_postlude_uses_actual_v2_theorem_and_state_serializer(self) -> None:
        serializer_source = subject.reference_protocol.FINGERPRINT_HELPER.read_text(
            encoding="utf-8",
        )
        self.assertIn(f'"{subject.FINGERPRINT_MARKER}\\t"', serializer_source)
        self.assertIn(f'"{subject.STATE_FINGERPRINT_MARKER}\\t"', serializer_source)
        with tempfile.TemporaryDirectory() as temporary:
            postlude = Path(temporary) / "postlude.ml"
            subject.write_postlude(
                postlude, Path(temporary), "05-lp_support-through-184",
                ["Linear_programming_results.linear_programming_results_th"],
                self.nonce,
            )
            source = postlude.read_text(encoding="utf-8")
        self.assertIn("candle_s1_emit_fingerprint", source)
        self.assertEqual(source.count("candle_s1_emit_state_fingerprint ();;"), 1)
        self.assertLess(
            source.index("candle_s1_emit_fingerprint"),
            source.index("candle_s1_emit_state_fingerprint"),
        )

    def test_fingerprint_boundary_requires_terminal_marker(self) -> None:
        boundary = "05-lp_support-through-184"
        theorem_names = subject.fingerprint_requests(boundary)
        source_log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            f"{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
        ])
        with self.assertRaisesRegex(subject.ContractError, "fingerprint success marker"):
            subject.validate_log(
                source_log, self.actions, boundary, self.nonce, theorem_names,
            )
        subject.validate_log(
            source_log + "\n" +
            f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 1",
            self.actions, boundary, self.nonce, theorem_names,
        )

    def test_fingerprint_protocol_namespace_and_session_are_closed(self) -> None:
        boundary = "05-lp_support-through-184"
        theorem_names = subject.fingerprint_requests(boundary)
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        action0 = f"{subject.ACTION_PREFIX} {self.nonce} 000 {'1' * 64}"
        action1 = f"{subject.ACTION_PREFIX} {self.nonce} 001 {'2' * 64}"
        success = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        terminal = (
            f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 1"
        )
        v2_record = f"{subject.FINGERPRINT_MARKER}\t00"
        valid = [preflight, action0, action1, success, v2_record, terminal]
        subject.validate_log(
            "\n".join(valid), self.actions, boundary, self.nonce, theorem_names,
        )
        for forged in (
            ["CANDLE_FINGERPRINT_V1\t00", *valid],
            [*valid, "CANDLE_STATE_FINGERPRINT_V3\t00"],
            [v2_record, *valid],
            [*valid, v2_record],
            [*valid, f"{subject.FINGERPRINT_SUCCESS_MARKER} {'b' * 32} forged 99"],
        ):
            with self.assertRaisesRegex(
                subject.ContractError,
                "unsupported or unexpected|outside its boundary session|terminal marker",
            ):
                subject.validate_log(
                    "\n".join(forged), self.actions, boundary, self.nonce,
                    theorem_names,
                )
        with self.assertRaisesRegex(
            subject.ContractError, "unsupported or unexpected stratum control record",
        ):
            subject.validate_log(
                "\n".join([
                    preflight, action0, action1, success,
                    f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 0",
                ]), self.actions, boundary, self.nonce,
            )

    def test_runtime_config_provides_exact_lp_certificate_list(self) -> None:
        certificates = [
            {"path": f"/inputs/easy_{index}.dat", "md5": f"{index:032x}"}
            for index in range(1, 40)
        ]
        prepared = {
            "flyspeck_root": Path("/flyspeck"),
            "overlay_root": Path("/overlay"),
            "generated_root": Path("/generated"),
            "boundary": {"boundary_id": "05-lp_support-through-184"},
            "actions": [
                {"identity_basename": "a.hl", "identity_md5": "1" * 32},
            ],
            "attempt_nonce": self.nonce,
            "normalized_runtime": [
                {"original": f"/o/{index}", "output": f"/n/{index}", "md5": "2" * 32}
                for index in range(18)
            ],
            "generated_runtime": certificates + [
                {"path": f"/inputs/other_{index}", "md5": "3" * 32}
                for index in range(4)
            ],
            "lp_certificate_runtime": certificates,
            "process_runtime": [
                {"path": "/metadata/date", "md5": "4" * 32},
                {"path": "/metadata/user", "md5": "5" * 32},
            ],
        }
        with tempfile.TemporaryDirectory() as temporary:
            config = Path(temporary) / "config.ml"
            subject.write_config(
                config, Path("/candle"), prepared,
                Path("/attempt/program.ml"), "6" * 32,
            )
            source = config.read_text(encoding="utf-8")
        certificate_block = source.split(
            "let candle_flyspeck_lp_certificate_files = [", 1
        )[1].split("];;", 1)[0]
        self.assertEqual(certificate_block.count("/inputs/easy_"), 39)
        self.assertNotIn("/inputs/other_", certificate_block)
        self.assertIn("let candle_flyspeck_stratum_normalization_count = 18;;", source)

    def test_snapshot_is_complete_deduplicated_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle-root"
            flyspeck = root / "flyspeck-root"
            overlay = root / "overlay-root"
            generated = root / "generated-root"
            output = root / "attempt"
            for directory in (candle, flyspeck, overlay, generated, output):
                directory.mkdir()

            def write(relative_root: Path, relative: Path | str,
                      content: bytes) -> tuple[Path, dict[str, object]]:
                path = relative_root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                return path, subject.hash_file(path)

            harness_records = {}
            for relative in (
                subject.SOURCE_DIGEST_RELATIVE,
                subject.SETUP_RELATIVE,
                subject.CHECK_RELATIVE,
                subject.FINGERPRINT_RELATIVE,
                subject.L2_TARGET_RELATIVE,
            ):
                _, record = write(candle, relative, relative.as_posix().encode())
                harness_records[relative.as_posix()] = record

            linked_outputs = {}
            for name in ("cake", "config_enc_str.txt", "candle_boot.ml"):
                path, record = write(candle, Path("candle/build") / name, name.encode())
                if name == "cake":
                    path.chmod(0o755)
                linked_outputs[name] = record
            _, linked_record = write(
                candle, subject.LINKED_RECORD_RELATIVE,
                json.dumps({"schema": 2}).encode(),
            )
            bootstrap_log, bootstrap_log_record = write(
                candle, "candle/build/bootstrap.log",
                b"verified bootstrap transcript",
            )
            bootstrap_record_value = {
                "schema": 1,
                "bootstrap_log": {
                    "path": "bootstrap.log",
                    "bytes": bootstrap_log_record["bytes"],
                    "sha256": bootstrap_log_record["sha256"],
                },
            }
            bootstrap_record, bootstrap_record_digest = write(
                candle, "candle/build/bootstrap-provenance.json",
                json.dumps(bootstrap_record_value).encode(),
            )
            linked_outputs["bootstrap.log"] = bootstrap_log_record
            linked_outputs["bootstrap-provenance.json"] = bootstrap_record_digest
            runtime_object, runtime_object_record = write(
                root, "libc.so.6", b"runtime object",
            )

            controller_sources = {}
            for module in subject.local_python_modules():
                label = Path(module.__file__).name
                source_bytes = module.__candle_source_bytes__
                source_path, source_record = write(
                    candle, Path("candle") / label, source_bytes,
                )
                controller_sources[label] = {
                    "source_path": str(source_path),
                    "execution_binding":
                        "compiled-from-captured-source-bytes",
                    "source_bytes": source_bytes,
                    **source_record,
                }
            runner_path, runner_record = write(
                candle, "candle/flyspeck_stratum_runtime.py",
                subject.RUNNER_SOURCE_BYTES,
            )
            controller_sources["flyspeck_stratum_runtime.py"] = {
                "source_path": str(runner_path),
                "execution_binding":
                    "startup-captured-after-initial-compilation",
                "source_bytes": subject.RUNNER_SOURCE_BYTES,
                **runner_record,
            }
            controller_execution = {
                "source_root": str(candle / "candle"),
                "direct_script_startup": {
                    "module_name": "__main__",
                    "spec_is_none": True,
                    "cached_is_none": True,
                    "argv0": str(runner_path),
                    "source_path": str(runner_path),
                },
                "commit_binding": {
                    "candle_commit": "f" * 40,
                    "sources": {
                        label: {
                            "repository_path": f"candle/{label}",
                            "index_tag": "H",
                            **{field: record[field]
                               for field in ("bytes", "sha256", "md5")},
                        }
                        for label, record in controller_sources.items()
                    },
                },
                "python_startup_flags": subject.EXPECTED_PYTHON_STARTUP_FLAGS,
                "python_startup_options":
                    subject.EXPECTED_PYTHON_STARTUP_OPTIONS,
                "initial_top_level_compilation_in_host_trust_boundary": True,
                "local_sources": controller_sources,
                "python_runtime": subject.validate_python_runtime(),
                "host_tools": subject.validate_controller_tools(),
                "git_environment": {
                    "LC_ALL": "C",
                    "PATH": "/usr/bin:/bin",
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_GLOBAL": "/dev/null",
                    "GIT_TERMINAL_PROMPT": "0",
                    "GIT_NO_REPLACE_OBJECTS": "1",
                    "GIT_OPTIONAL_LOCKS": "0",
                },
            }

            source, source_record = write(flyspeck, "source.ml", b"source")
            normalized, normalized_record = write(overlay, "source.ml", b"normalized")
            certificate, certificate_record = write(generated, "cert.out", b"certificate")
            process_input, process_record = write(candle, "metadata/date", b"fixed date")
            prefix, prefix_record = write(root, "prefix.ml", b'#flyspeck_needs "source.ml";;\n')
            prefix_record = {"path": "prefix.ml", **prefix_record}

            prepared = {
                "source_runtime": [{
                    "repository": "flyspeck", "path": "source.ml",
                    "absolute": str(source), **source_record,
                }],
                "harness_records": harness_records,
                "normalized_runtime": [{
                    "relative": "source.ml", "original_relative": "source.ml",
                    "original": str(source), "output": str(normalized),
                    **normalized_record,
                }],
                "generated_runtime": [{
                    "class": "lp-certificate-prepared", "relative": "cert.out",
                    "path": str(certificate), **certificate_record,
                }],
                "lp_certificate_runtime": [{"relative": "cert.out"}],
                "process_runtime": [{
                    "relative": "metadata/date", "path": str(process_input),
                    **process_record,
                }],
                "prefix_path": prefix,
                "prefix_record": prefix_record,
                "linked_record": linked_record,
            }
            runtime, snapshot = subject.create_runtime_snapshot(
                output, candle, prepared, {
                    "outputs": linked_outputs,
                    "runtime_elf_closure": {
                        "policy":
                            subject.cakeml_artifact_provenance
                            .ELF_DYNAMIC_CLOSURE_POLICY,
                        "dynamic_path_tags": {},
                        "files": {
                            str(runtime_object): runtime_object_record,
                        },
                        "roles": {"libc.so.6": str(runtime_object)},
                        "virtual_objects": [],
                    },
                }, controller_execution,
            )
            subject.validate_runtime_snapshot(snapshot, output)
            self.assertEqual(
                runtime["prefix_path"].read_bytes(), prefix.read_bytes(),
            )
            source_entry = next(
                record for record in snapshot["files"]
                if record["path"] == "flyspeck/source.ml"
            )
            self.assertEqual(source_entry["classes"], ["source:flyspeck"])
            self.assertEqual(len({item["path"] for item in snapshot["files"]}),
                             snapshot["file_count"])
            self.assertTrue(any(
                item["path"] ==
                "candle/candle/build/cakeml-build-provenance.json"
                and item["classes"] == ["linked-provenance-record"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"].startswith("runtime-elf/")
                and item["classes"] == ["archived-runtime-elf"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"] ==
                "candle/candle/build/bootstrap-provenance.json"
                and item["classes"] == ["linked-runtime"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"] == "candle/candle/build/bootstrap.log"
                and item["classes"] == ["linked-runtime"]
                for item in snapshot["files"]
            ))
            retained_runner = next(
                item for item in snapshot["controller_execution"]["local_sources"]
                if item["label"] == "flyspeck_stratum_runtime.py"
            )
            self.assertEqual(
                (output / "snapshot" / retained_runner["path"]).read_bytes(),
                subject.RUNNER_SOURCE_BYTES,
            )
            self.assertTrue(any(
                item["classes"] == ["controller-python-executable"]
                for item in snapshot["files"]
            ))
            self.assertEqual(
                {item["label"] for item in
                 snapshot["controller_execution"]["host_tools"]},
                set(subject.EXPECTED_CONTROLLER_TOOLS),
            )
            self.assertEqual(
                snapshot["controller_execution"]["python_runtime"]
                ["elf_dynamic_path_tags"],
                {},
            )

            malformed = copy.deepcopy(snapshot)
            malformed["schema"] = 1
            with self.assertRaisesRegex(subject.ContractError, "snapshot schema"):
                subject.validate_runtime_snapshot(malformed, output)
            malformed = copy.deepcopy(snapshot)
            malformed["controller_execution"]["python_runtime"]["version"] = "other"
            with self.assertRaisesRegex(
                subject.ContractError, "Python execution identity mismatch",
            ):
                subject.validate_runtime_snapshot(malformed, output)
            malformed = copy.deepcopy(snapshot)
            malformed["controller_execution"]["python_runtime"][
                "elf_dynamic_path_tags"
            ] = {"RUNPATH": ["/injected"]}
            with self.assertRaisesRegex(
                subject.ContractError, "Python ELF metadata mismatch",
            ):
                subject.validate_runtime_snapshot(malformed, output)

            snapshot_root = output / "snapshot"
            snapshot_root.chmod(0o755)
            extra = snapshot_root / "unrecorded"
            extra.write_bytes(b"not in the closure")
            with self.assertRaisesRegex(subject.ContractError, "unrecorded.*files"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.unlink()
            extra.mkdir()
            with self.assertRaisesRegex(subject.ContractError, "unrecorded.*directories"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.rmdir()
            extra.symlink_to(snapshot_root / "flyspeck/source.ml")
            with self.assertRaisesRegex(subject.ContractError, "contains a symlink"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.unlink()
            snapshot_root.chmod(0o555)

            retained_runner_path = snapshot_root / retained_runner["path"]
            retained_runner_path.chmod(0o644)
            retained_runner_path.write_bytes(b"tampered controller")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.validate_runtime_snapshot(snapshot, output)
            retained_runner_path.write_bytes(subject.RUNNER_SOURCE_BYTES)
            retained_runner_path.chmod(0o444)

            snapshot_source = output / "snapshot/flyspeck/source.ml"
            snapshot_source.chmod(0o644)
            snapshot_source.write_bytes(b"tampered")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.validate_runtime_snapshot(snapshot, output)

    def test_runner_cli_requires_isolated_python(self) -> None:
        runner = Path(subject.__file__).resolve()
        ordinary = subprocess.run(
            ["/usr/bin/python3", str(runner), "--help"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertNotEqual(ordinary.returncode, 0)
        self.assertIn("Python startup flags mismatch", ordinary.stdout)
        for flags in (
            ("-I",),
            ("-S",),
            ("-I", "-S", "-O"),
            ("-I", "-S", "-X", "tracemalloc"),
            ("-I", "-S", "-W", "error"),
            ("-I", "-S", "-u"),
        ):
            rejected = subprocess.run(
                ["/usr/bin/python3", *flags, str(runner), "--help"],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertRegex(
                rejected.stdout, r"Python startup (?:flags|options) mismatch",
            )
        isolated = subprocess.run(
            ["/usr/bin/python3", "-I", "-S", str(runner), "--help"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertEqual(isolated.returncode, 0, isolated.stdout)

        imported = subprocess.run(
            [
                "/usr/bin/python3", "-I", "-S", "-c",
                (
                    "import importlib.util,pathlib;"
                    f"p=pathlib.Path({str(runner)!r});"
                    "s=importlib.util.spec_from_file_location('imported_runner',p);"
                    "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
                    "m.main()"
                ),
            ],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertNotEqual(imported.returncode, 0)
        self.assertIn("execute directly from its .py source", imported.stdout)

    def test_local_modules_execute_from_captured_source_bytes(self) -> None:
        for module in subject.local_python_modules():
            source = module.__candle_source_bytes__
            self.assertEqual(
                hashlib.sha256(source).hexdigest(),
                module.__candle_source_sha256__,
            )
            self.assertEqual(Path(module.__file__).read_bytes(), source)

    def test_all_controller_git_calls_share_the_fail_closed_policy(self) -> None:
        expected_environment = subject.flyspeck_stratum_plan.GIT_ENVIRONMENT
        self.assertEqual(
            subject.cakeml_artifact_provenance.git_environment(),
            expected_environment,
        )
        command = subject.cakeml_artifact_provenance.git_command(
            Path("/repository"), "status",
        )
        self.assertEqual(
            tuple(command[1:7]), subject.flyspeck_stratum_plan.GIT_OPTIONS,
        )

    def test_exact_source_loader_ignores_adjacent_bytecode(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "helper.py"
            cache = root / "__pycache__/helper.cpython-312.pyc"
            cache.parent.mkdir()
            source.write_text("VALUE = 'cached!'\n", encoding="utf-8")
            source_stat = source.stat()
            py_compile.compile(str(source), cfile=str(cache), doraise=True)
            source.write_text("VALUE = 'source!'\n", encoding="utf-8")
            os.utime(
                source,
                ns=(source_stat.st_atime_ns, source_stat.st_mtime_ns),
            )
            sys.path.insert(0, str(root))
            try:
                ordinary = importlib.import_module("helper")
                self.assertEqual(ordinary.VALUE, "cached!")
            finally:
                sys.modules.pop("helper", None)
                sys.path.pop(0)
            name = "_candle_stratum_test_exact_source"
            try:
                module = subject._load_local_source(name, source.resolve())
                self.assertEqual(module.VALUE, "source!")
                self.assertEqual(
                    module.__candle_source_bytes__, source.read_bytes(),
                )
            finally:
                sys.modules.pop(name, None)

    def test_exact_source_loader_rejects_preloaded_collision(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "helper.py"
            source.write_text("VALUE = 1\n", encoding="utf-8")
            name = "_candle_stratum_test_preloaded"
            sys.modules[name] = types.ModuleType(name)
            try:
                with self.assertRaisesRegex(RuntimeError, "untrusted preloaded"):
                    subject._load_local_source(name, source.resolve())
            finally:
                sys.modules.pop(name, None)

    def test_snapshot_copy_rejects_bytes_not_bound_by_expected_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.write_bytes(b"changed after validation")
            expected = subject.hash_file(source)
            expected["sha256"] = "0" * 64
            with self.assertRaisesRegex(subject.ContractError, "snapshot sha256 mismatch"):
                subject.snapshot_copy(source, root / "snapshot", "source", expected)

    def test_pre_attempt_failure_removes_only_new_incomplete_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "new-attempt"

            def fail_preflight(*arguments):
                ownership = arguments[-1]
                snapshot = output / "snapshot/readonly"
                snapshot.mkdir(parents=True)
                (snapshot / "partial").write_bytes(b"partial")
                snapshot.chmod(0o555)
                opened = output.stat()
                marker = output / ".candle-preflight-owner"
                marker.write_text(ownership["nonce"] + "\n", encoding="ascii")
                ownership.update({
                    "created": True,
                    "device": opened.st_dev,
                    "inode": opened.st_ino,
                    "marker_path": marker,
                    "marker_ready": True,
                })
                raise subject.ContractError("injected preflight failure")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=fail_preflight,
            ):
                with self.assertRaisesRegex(
                    subject.ContractError, "injected preflight failure",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertFalse(output.exists())

    def test_lost_output_race_never_deletes_competing_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "competing-attempt"

            def lose_race(*_arguments):
                output.mkdir()
                (output / "competitor").write_bytes(b"owned elsewhere")
                raise subject.ContractError("output already exists")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=lose_race,
            ):
                with self.assertRaisesRegex(
                    subject.ContractError, "output already exists",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertEqual(
                (output / "competitor").read_bytes(), b"owned elsewhere",
            )

    def test_owned_empty_directory_is_cleaned_if_marker_creation_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "attempt"

            def fail_marker(*arguments):
                ownership = arguments[-1]
                output.mkdir()
                opened = output.stat()
                ownership.update({
                    "created": True,
                    "device": opened.st_dev,
                    "inode": opened.st_ino,
                    "marker_ready": False,
                })
                raise OSError("injected marker failure")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=fail_marker,
            ):
                with self.assertRaisesRegex(OSError, "injected marker failure"):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertFalse(output.exists())

    def test_outer_wrapper_restores_handlers_after_internal_escape(self) -> None:
        original_term = signal.getsignal(signal.SIGTERM)
        original_int = signal.getsignal(signal.SIGINT)
        original_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())

        def escape(*_arguments):
            signal.signal(signal.SIGTERM, lambda *_ignored: None)
            signal.signal(signal.SIGINT, lambda *_ignored: None)
            signal.pthread_sigmask(
                signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT},
            )
            raise RuntimeError("injected internal escape")

        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "attempt"
            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=escape,
            ):
                with self.assertRaisesRegex(
                    RuntimeError, "injected internal escape",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
        self.assertIs(signal.getsignal(signal.SIGTERM), original_term)
        self.assertIs(signal.getsignal(signal.SIGINT), original_int)
        self.assertEqual(
            signal.pthread_sigmask(signal.SIG_BLOCK, set()), original_mask,
        )

    def test_internal_attempt_rejects_raw_plan_root_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "plan-target"
            target.mkdir()
            plan_link = root / "plan-link"
            plan_link.symlink_to(target, target_is_directory=True)
            with self.assertRaisesRegex(
                subject.ContractError, "stratum plan root must not be a symlink",
            ):
                subject._run_attempt_impl(
                    root / "missing-candle.sh", plan_link, "boundary",
                    root / "attempt", 1, 1, 1, 1,
                )

    def test_lp_certificate_runtime_uses_contract_order_not_source_order(self) -> None:
        expected = [f"easy_{index}.dat" for index in range(1, 39)] + [
            "hard_7.dat",
        ]
        source_order = [
            {
                "class": "lp-certificate-prepared" if name == "hard_7.dat"
                else "lp-certificate",
                "relative": f"formal_lp/glpk/binary/{name}",
            }
            for name in reversed(expected)
        ]
        ordered = subject.order_lp_certificate_runtime(source_order, expected)
        self.assertEqual(
            [Path(item["relative"]).name for item in ordered], expected,
        )
        source_order[-1]["relative"] = "formal_lp/glpk/binary/unexpected.dat"
        with self.assertRaisesRegex(subject.ContractError,
                                    "certificate basename set mismatch"):
            subject.order_lp_certificate_runtime(source_order, expected)

    def test_child_resource_limiter_installs_all_three_limits(self) -> None:
        cpu_seconds = 17
        address_space = 2 * subject.GIB
        output_file = subject.GIB
        installer = subject.process_limit_preexec(
            cpu_seconds, address_space, output_file,
        )
        code = (
            "import json,resource; "
            "print(json.dumps([resource.getrlimit(resource.RLIMIT_CPU),"
            "resource.getrlimit(resource.RLIMIT_AS),"
            "resource.getrlimit(resource.RLIMIT_FSIZE)]))"
        )
        completed = subprocess.run(
            [sys.executable, "-c", code], check=True, text=True,
            stdout=subprocess.PIPE, preexec_fn=installer,
        )
        self.assertEqual(json.loads(completed.stdout), [
            [cpu_seconds, cpu_seconds],
            [address_space, address_space],
            [output_file, output_file],
        ])


if __name__ == "__main__":
    unittest.main()
