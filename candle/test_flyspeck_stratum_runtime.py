#!/usr/bin/env python3

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
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
        fields = [
            subject.FINGERPRINT_MARKER,
            name.encode().hex(),
            b"theorem".hex(), b"hypotheses".hex(), b"conclusion".hex(),
            b"axioms".hex(), "0", "3",
        ]
        report = subject.parse_fingerprints(
            "\t".join(fields), [name], Path(subject.__file__).resolve(),
        )
        self.assertEqual(report["status"], "observed_uncompared")
        self.assertFalse(report["approved_reference_present"])
        self.assertEqual(
            report["theorems"][0]["theorem_sha256"],
            hashlib.sha256(b"theorem").hexdigest(),
        )
        bad = fields.copy()
        bad[-1] = "4"
        with self.assertRaisesRegex(subject.ContractError, "global axiom count"):
            subject.parse_fingerprints(
                "\t".join(bad), [name], Path(subject.__file__).resolve(),
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
                root, "bootstrap.log", b"verified bootstrap transcript",
            )
            bootstrap_record_value = {
                "schema": 1,
                "bootstrap_log": {
                    "path": str(bootstrap_log),
                    "bytes": bootstrap_log_record["bytes"],
                    "sha256": bootstrap_log_record["sha256"],
                },
            }
            bootstrap_record, bootstrap_record_digest = write(
                root, "bootstrap-record.json",
                json.dumps(bootstrap_record_value).encode(),
            )
            runtime_object, runtime_object_record = write(
                root, "libc.so.6", b"runtime object",
            )

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
                    "bootstrap_record_path": str(bootstrap_record),
                    "bootstrap_record": bootstrap_record_digest,
                    "runtime_elf_closure": {
                        "files": {
                            str(runtime_object): runtime_object_record,
                        },
                    },
                },
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
                item["path"] == "provenance/bootstrap-record.json"
                and item["classes"] == ["bootstrap-provenance-record"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"] == "provenance/bootstrap.log"
                and item["classes"] == ["bootstrap-proof-log"]
                for item in snapshot["files"]
            ))

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
            snapshot_root.chmod(0o555)

            snapshot_source = output / "snapshot/flyspeck/source.ml"
            snapshot_source.chmod(0o644)
            snapshot_source.write_bytes(b"tampered")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.validate_runtime_snapshot(snapshot, output)

    def test_snapshot_copy_rejects_bytes_not_bound_by_expected_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.write_bytes(b"changed after validation")
            expected = subject.hash_file(source)
            expected["sha256"] = "0" * 64
            with self.assertRaisesRegex(subject.ContractError, "snapshot sha256 mismatch"):
                subject.snapshot_copy(source, root / "snapshot", "source", expected)

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
