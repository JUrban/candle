#!/usr/bin/env python3

import copy
import json
import re
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cakeml_artifact_provenance as subject


def successful_bootstrap_log(build_command: str) -> str:
    lines = ["Holmake: Building 18 theory files"] + [
        f"Holmake: [{index}/18] {target}"
        for index, target in enumerate(subject.BOOTSTRAP_TARGETS[:-1], 1)
    ] + [
        "Writing cv to file: cake.S",
        'Exporting theory "x64Bootstrap" ... done.',
        "Holmake: [18/18] x64Bootstrap",
    ]
    for label in subject.GNU_TIME_FOOTER_LABELS:
        if label == "Command being timed":
            value = f'"{build_command}"'
        elif label == "Exit status":
            value = "0"
        elif label == "Percent of CPU this job got":
            value = "100%"
        elif label == "Elapsed (wall clock) time (h:mm:ss or m:ss)":
            value = "0:01.00"
        else:
            value = "0"
        lines.append(f"\t{label}: {value}")
    return "\n".join(lines) + "\n"


def build_small_installed_elf(build: Path, *, return_code: int = 0) -> None:
    (build / "cake.S").write_text(
        ".text\n.section .note.GNU-stack,\"\",@progbits\n",
        encoding="utf-8",
    )
    (build / "basis_ffi.c").write_text(
        f"int main(void) {{ return {return_code}; }}\n",
        encoding="utf-8",
    )
    (build / "Makefile").write_text(
        "cake: cake.S basis_ffi.c\n"
        "\t$(CC) $(CFLAGS) $< basis_ffi.c $(LOADLIBES) $(EVALFLAG) "
        "-o $@ $(LDFLAGS) $(LDLIBS)\n",
        encoding="utf-8",
    )
    arguments = list(subject.NATIVE_LINK_MAKE_ARGV)
    arguments[arguments.index(
        "CC=/usr/bin/cc -B.candle-native-tools/"
    )] = "CC=/usr/bin/cc"
    arguments[arguments.index(
        "CFLAGS=-O2 -save-temps=obj -v"
    )] = "CFLAGS=-O2"
    subprocess.run(
        arguments, check=True, cwd=build,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
    )


class CakeMLArtifactProvenanceTests(unittest.TestCase):
    def test_manifest_pins_exact_dopen_stack(self) -> None:
        candle_root = Path(__file__).resolve().parent.parent
        pins = subject.expected_pins(candle_root)
        self.assertEqual(
            pins["cakeml_commit"],
            "0e97a1ab86924e905e1d1c893191651197b82f6e",
        )
        self.assertEqual(
            pins["hol4_commit"],
            "a390cbabd3a4521bab4ee20281e3e42933a8a3ae",
        )

    def test_documented_linked_schema_tracks_implementation(self) -> None:
        candle_root = Path(__file__).resolve().parent.parent
        current = f"schema-{subject.LINKED_PROVENANCE_SCHEMA} linked-provenance"
        current_bootstrap = (
            f"schema-{subject.BOOTSTRAP_PROVENANCE_SCHEMA} final bootstrap record"
        )
        performance = (
            candle_root / "candle/compatibility/flyspeck_float_performance.md"
        ).read_text(encoding="utf-8")
        self.assertIn(current, performance)
        acceptance = (
            candle_root / "candle/compatibility/dopen_direct_acceptance.md"
        ).read_text(encoding="utf-8")
        self.assertIn(current_bootstrap, acceptance)
        self.assertIn(
            f"schema-{subject.LINKED_PROVENANCE_SCHEMA} "
            "`candle/build/cakeml-build-provenance.json`",
            acceptance,
        )
        for path in candle_root.rglob("*.md"):
            text = path.read_text(encoding="utf-8")
            for match in re.finditer(
                r"schema-([0-9]+) linked-provenance", text,
            ):
                self.assertEqual(
                    int(match.group(1)), subject.LINKED_PROVENANCE_SCHEMA,
                    f"stale linked schema in {path}",
                )

    def test_file_record_rejects_tampering(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input"
            path.write_bytes(b"first")
            record = subject.file_record(path)
            subject.validate_file_record(path, record, "test")
            path.write_bytes(b"second")
            with self.assertRaisesRegex(subject.ProvenanceError, "mismatch"):
                subject.validate_file_record(path, record, "test")

    def test_ordinary_file_identity_rejects_path_swap_during_capture(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / "input"
            old = root / "old"
            path.write_bytes(b"authenticated bytes")
            real_read = subject.os.read
            swapped = False

            def swapping_read(descriptor: int, count: int) -> bytes:
                nonlocal swapped
                block = real_read(descriptor, count)
                if block and not swapped:
                    swapped = True
                    path.rename(old)
                    path.write_bytes(b"replacement")
                return block

            with mock.patch.object(subject.os, "read", side_effect=swapping_read):
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "file (?:path )?changed",
                ):
                    subject.ordinary_file_identity(path)

    def test_atomic_receipt_is_removed_when_publication_postcheck_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            receipt = root / "receipt.json"

            def reject() -> None:
                raise subject.ProvenanceError("signal before completion boundary")

            with self.assertRaisesRegex(
                subject.ProvenanceError, "completion boundary",
            ):
                subject.write_new_json(
                    receipt, {"state": "complete"}, after_publish=reject,
                )
            self.assertFalse(receipt.exists())
            self.assertEqual(list(root.iterdir()), [])

    def test_retained_python_controller_allows_new_checker_process_identity(self) -> None:
        executable = subject.executable_tool_record(Path("/usr/bin/python3"))
        source_bytes = b"controller source"
        source_record = subject.bytes_record(source_bytes)
        record = {
            "policy": "direct_usr_bin_python3_isolated_controller_v1",
            "executable": executable,
            "elf_closure": subject.elf_dynamic_closure(Path("/usr/bin/python3")),
            "proc_self_exe": executable["resolved_path"],
            "sys_executable": "/usr/bin/python3",
            "sys_version": "recorded-version",
            "flags": {
                "isolated": 1, "ignore_environment": 1, "no_user_site": 1,
                "no_site": 1, "safe_path": True, "utf8_mode": 1,
            },
            "xoptions": {},
            "warnoptions": [],
            "argv": ["/candle/candle/cakeml_artifact_provenance.py",
                     "run-bootstrap"],
            "module": {"name": "__main__", "spec": None, "cached": None},
            "process": {"pid": 100, "start_time_ticks": 200},
            "source": {
                "repository_path": "candle/cakeml_artifact_provenance.py",
                "path": "/candle/candle/cakeml_artifact_provenance.py",
                **source_record,
                "commit_blob": source_record,
            },
        }
        observed = copy.deepcopy(record)
        observed["argv"] = [record["argv"][0], "check-bootstrap"]
        observed["process"] = {"pid": 300, "start_time_ticks": 400}
        with mock.patch.object(
            subject, "python_controller_record", return_value=observed,
        ):
            subject.validate_python_controller_record(
                record, candle_root=Path("/candle"),
            )

    def test_version_details_extracts_exact_revisions(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / "cake"
            executable.write_text(
                "#!/bin/sh\n"
                "printf '%s\\n' 'The CakeML compiler' "
                "'CakeML: cake-commit' 'HOL4:   hol-commit'\n",
                encoding="utf-8",
            )
            executable.chmod(0o755)
            cake, hol, output = subject.version_details(executable)
        self.assertEqual((cake, hol), ("cake-commit", "hol-commit"))
        self.assertIn("The CakeML compiler", output)

    def test_version_details_rejects_ambiguous_identity(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            executable = Path(directory) / "cake"
            executable.write_text(
                "#!/bin/sh\nprintf '%s\\n' 'CakeML: one' 'CakeML: two' 'HOL4: h'\n",
                encoding="utf-8",
            )
            executable.chmod(0o755)
            with self.assertRaisesRegex(subject.ProvenanceError, "ambiguous"):
                subject.version_details(executable)

    def test_elf_dynamic_closure_pins_loaded_libc(self) -> None:
        executable = Path("/bin/true")
        closure = subject.elf_dynamic_closure(executable)
        self.assertEqual(
            closure["policy"],
            "ldd_roles_resolved_absolute_paths_and_content_v3",
        )
        self.assertEqual(closure["dynamic_path_tags"], {})
        self.assertTrue(closure["files"])
        self.assertEqual(set(closure["roles"].values()), set(closure["files"]))
        self.assertTrue(any(
            Path(path).name.startswith("libc.so")
            for path in closure["files"]
        ))
        subject.validate_elf_dynamic_closure(executable, closure)

    def test_elf_dynamic_closure_rejects_tampered_record(self) -> None:
        executable = Path("/bin/true")
        closure = subject.elf_dynamic_closure(executable)
        path = next(iter(closure["files"]))
        closure["files"][path]["sha256"] = "0" * 64
        with self.assertRaisesRegex(
            subject.ProvenanceError, "closure mismatch",
        ):
                subject.validate_elf_dynamic_closure(executable, closure)

    def test_bootstrap_log_requires_one_exact_trailing_gnu_time_footer(self) -> None:
        command = "env HOLDIR=/hol /hol/bin/Holmake -j1 cake.S"
        log = successful_bootstrap_log(command)
        subject.validate_bootstrap_log(log, command)
        with self.assertRaisesRegex(
            subject.ProvenanceError, "duplicate or missing successful",
        ):
            subject.validate_bootstrap_log(
                log.replace(
                    "Writing cv to file: cake.S\n",
                    "\tExit status: 0\nWriting cv to file: cake.S\n",
                ),
                command,
            )
        with self.assertRaisesRegex(
            subject.ProvenanceError, "command does not match",
        ):
            subject.validate_bootstrap_log(log + "trailing output\n", command)

    def test_bootstrap_log_rejects_spoofed_success_before_failure(self) -> None:
        command = "env HOLDIR=/hol /hol/bin/Holmake -j1 cake.S"
        log = successful_bootstrap_log(command)
        log = log.replace(
            "Writing cv to file: cake.S\n",
            "\tExit status: 0\nCommand exited with non-zero status 1\n"
            "Writing cv to file: cake.S\n",
        ).replace("\tExit status: 0\n", "\tExit status: 1\n", 1)
        with self.assertRaises(subject.ProvenanceError):
            subject.validate_bootstrap_log(log, command)

    def test_bootstrap_log_rejects_warm_tree_x64_only_transcript(self) -> None:
        command = "/hol/bin/Holmake -j1 cake.S"
        log = successful_bootstrap_log(command)
        for index, target in enumerate(subject.BOOTSTRAP_TARGETS[:-1], 1):
            log = log.replace(f"Holmake: [{index}/18] {target}\n", "")
        with self.assertRaisesRegex(
            subject.ProvenanceError, "exact ordered 18-target rebuild",
        ):
            subject.validate_bootstrap_log(log, command)

    def test_bootstrap_forced_outputs_exclude_tracked_side_inputs(self) -> None:
        root = Path("/authenticated/cakeml")
        paths = subject.bootstrap_forced_output_paths(root)
        relatives = [relative for relative, _ in paths]
        self.assertEqual(len(paths), 2 + 17 * 6 + 4)
        self.assertIn(
            "compiler/bootstrap/compilation/x64/64/cake.S", relatives,
        )
        self.assertNotIn(
            "compiler/bootstrap/compilation/x64/64/candle_boot.ml", relatives,
        )
        self.assertIn(
            "compiler/bootstrap/compilation/x64/64/config_enc_str.txt", relatives,
        )

    def test_bootstrap_output_inventory_rejects_path_escape(self) -> None:
        root = Path("/authenticated/cakeml")
        receipt = Path("/evidence/preflight.json")
        archive = subject._bootstrap_archive_root(receipt)
        record = {
            "receipt_path": str(receipt),
            "forced_outputs": {
                "preimage_archive_root": str(archive),
                "entries": [
                    {
                        "relative": relative,
                        "path": str(path),
                        "postcondition": postcondition,
                        "preimage_archive_path": str(archive / relative),
                    }
                    for relative, path, postcondition in
                    subject.bootstrap_cleanup_output_paths(root)
                ],
            },
        }
        subject.validate_bootstrap_output_path_inventory(record, root)
        victim = Path("/tmp/arbitrary-victim")
        record["forced_outputs"]["entries"][0]["path"] = str(victim)
        with self.assertRaisesRegex(
            subject.ProvenanceError, "path inventory mismatch",
        ):
            subject.validate_bootstrap_output_path_inventory(record, root)

    def test_bootstrap_symlink_inputs_bind_link_blob_and_in_root_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            bootstrap = root / subject.BOOTSTRAP_RELATIVE
            bootstrap.mkdir(parents=True)
            for name, (link_text, target_relative) in (
                subject.BOOTSTRAP_SYMLINK_INPUTS.items()
            ):
                target = root / target_relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(f"target {name}\n", encoding="utf-8")
                (bootstrap / name).symlink_to(link_text)
            subprocess.run(
                ["/usr/bin/git", "init", "-q"], cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            subprocess.run(
                ["/usr/bin/git", "add", "."], cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            subprocess.run(
                ["/usr/bin/git", "-c", "user.name=Test", "-c",
                 "user.email=test@example.invalid", "commit", "-qm", "inputs"],
                cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            records = {
                name: subject.bootstrap_symlink_input_record(root, name)
                for name in subject.BOOTSTRAP_SYMLINK_INPUTS
            }
            for name, record in records.items():
                subject.validate_bootstrap_symlink_input_record(
                    record, name, root, require_live=True,
                )
            link = bootstrap / "candle_boot.ml"
            link_text = link.readlink()
            link.unlink()
            link.symlink_to(link_text)
            with self.assertRaisesRegex(
                subject.ProvenanceError, "symlink input changed",
            ):
                subject.validate_bootstrap_symlink_input_record(
                    records["candle_boot.ml"], "candle_boot.ml", root,
                    require_live=True,
                )

    def test_bootstrap_preparation_removes_and_archives_stale_config(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence = root / "evidence"
            evidence.mkdir()
            receipt = evidence / "preflight.json"
            archive = subject._bootstrap_archive_root(receipt)
            entries = []
            stale_names = {
                "cake.S", "config_enc_str.txt", "compiler64ProgScript.ui",
            }
            for relative, path, postcondition in (
                subject.bootstrap_cleanup_output_paths(root)
            ):
                preimage = None
                if path.name in stale_names:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(f"stale {path.name}\n", encoding="utf-8")
                    preimage = subject.ordinary_file_identity(path)
                entries.append({
                    "relative": relative,
                    "path": str(path),
                    "postcondition": postcondition,
                    "preimage": preimage,
                    "preimage_archive_path": str(archive / relative),
                })
            preflight = {
                "forced_outputs": {
                    "preimage_archive_root": str(archive),
                    "entries": entries,
                },
            }
            with mock.patch.object(
                subject, "validate_bootstrap_preflight", return_value=None,
            ):
                subject.prepare_bootstrap_output(
                    root, root, root, preflight,
                )
            paths = {
                path.name: (relative, path)
                for relative, path, _ in subject.bootstrap_cleanup_output_paths(root)
                if path.name in stale_names
            }
            for name in stale_names:
                relative, target = paths[name]
                self.assertFalse(target.exists())
                archived = archive / relative
                self.assertEqual(archived.read_text(encoding="utf-8"),
                                 f"stale {name}\n")

    def test_bootstrap_preparation_archives_both_malicious_lastmakers(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            evidence = root / "evidence"
            evidence.mkdir()
            receipt = evidence / "preflight.json"
            archive = subject._bootstrap_archive_root(receipt)
            entries = []
            lastmakers = set(subject.bootstrap_lastmaker_output_paths(root))
            for relative, path, postcondition in (
                subject.bootstrap_cleanup_output_paths(root)
            ):
                preimage = None
                if (relative, path) in lastmakers:
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b"/bin/true\n")
                    preimage = subject.ordinary_file_identity(path)
                entries.append({
                    "relative": relative,
                    "path": str(path),
                    "postcondition": postcondition,
                    "preimage": preimage,
                    "preimage_archive_path": str(archive / relative),
                })
            preflight = {
                "forced_outputs": {
                    "preimage_archive_root": str(archive),
                    "entries": entries,
                },
            }
            with mock.patch.object(
                subject, "validate_bootstrap_preflight", return_value=None,
            ):
                subject.prepare_bootstrap_output(root, root, root, preflight)
            for relative, path in lastmakers:
                self.assertFalse(path.exists())
                self.assertEqual((archive / relative).read_bytes(), b"/bin/true\n")

    def test_bootstrap_transition_rejects_alternate_lastmaker_postimage(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            hol_root = root / "hol"
            path = root / "translation/.hol/make-deps/lastmaker"
            path.parent.mkdir(parents=True)
            path.write_bytes(b"/bin/true\n")
            output = {
                "relative": "translation/.hol/make-deps/lastmaker",
                "path": str(path),
                "postcondition": "exact_holmake_lastmaker",
                "preimage": None,
                "preimage_archive_path": str(root / "archive/lastmaker"),
            }
            preflight = {
                "hol4_root": str(hol_root),
                "forced_outputs": {"entries": [output]},
            }
            transition = {
                "relative": output["relative"],
                "postcondition": output["postcondition"],
                "preimage": None,
                "preimage_archive": None,
                "postimage": subject.ordinary_file_identity(path),
            }
            with self.assertRaisesRegex(
                subject.ProvenanceError, "does not name pinned Holmake",
            ):
                subject.validate_bootstrap_forced_output_transitions(
                    preflight, [transition], require_live=False,
                )

    def test_ancestor_inventory_excludes_fresh_stratum_and_detects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            objects = root / "unrelated/theory/.hol/objs"
            objects.mkdir(parents=True)
            ancestor = objects / "AncestorTheory.dat"
            ancestor.write_bytes(b"ancestor")
            managed = dict(subject.bootstrap_forced_output_paths(root))[
                "compiler/bootstrap/translation/.hol/objs/pancake_lexProgTheory.dat"
            ]
            managed.parent.mkdir(parents=True, exist_ok=True)
            managed.write_bytes(b"fresh-stratum-preimage")
            inventory = subject.bootstrap_ancestor_artifact_inventory(root)
            self.assertEqual(
                [entry["relative"] for entry in inventory["entries"]],
                ["unrelated/theory/.hol/objs/AncestorTheory.dat"],
            )
            ancestor.write_bytes(b"changed")
            with self.assertRaisesRegex(
                subject.ProvenanceError, "inventory changed",
            ):
                subject.validate_bootstrap_ancestor_artifact_inventory(
                    inventory, root, require_live=True,
                )

    def test_hol_proof_artifact_inventory_binds_objects_links_and_generated(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            objects = root / "src/theory/.hol/objs"
            objects.mkdir(parents=True)
            object_file = objects / "ObjectTheory.uo"
            object_file.write_bytes(b"object")
            payload = root / "src/theory/Payload.sml"
            payload.write_bytes(b"payload")
            generated = root / "generated.sml"
            generated.write_bytes(b"generated")
            sigobj = root / "sigobj"
            sigobj.mkdir()
            (sigobj / "Systeml.sig").write_bytes(b"ordinary sigobj")
            (sigobj / "Payload.sml").symlink_to("../src/theory/Payload.sml")
            object_paths_digest = subject._canonical_json_sha256([
                "src/theory/.hol/objs/ObjectTheory.uo",
            ])
            sigobj_contracts_digest = subject._canonical_json_sha256([
                ["symlink", "sigobj/Payload.sml", "../src/theory/Payload.sml",
                 "src/theory/Payload.sml"],
                ["ordinary", "sigobj/Systeml.sig"],
            ])
            with mock.patch.object(
                subject, "HOL_PROOF_OBJECT_COUNT", 1,
            ), mock.patch.object(
                subject, "HOL_SIGOBJ_ORDINARY_COUNT", 1,
            ), mock.patch.object(
                subject, "HOL_SIGOBJ_SYMLINK_COUNT", 1,
            ), mock.patch.object(
                subject, "HOL_GENERATED_PROOF_INPUTS", ("generated.sml",),
            ), mock.patch.object(
                subject, "HOL_PROOF_OBJECT_PATHS_SHA256", object_paths_digest,
            ), mock.patch.object(
                subject, "HOL_SIGOBJ_CONTRACTS_SHA256", sigobj_contracts_digest,
            ):
                inventory = subject.hol_proof_artifact_inventory(root)
                subject.validate_hol_proof_artifact_inventory(
                    inventory, root, require_live=True,
                )
                link = next(
                    entry for entry in inventory["sigobj_entries"]
                    if entry["kind"] == "symlink"
                )
                self.assertEqual(link["link_text"], "../src/theory/Payload.sml")
                self.assertEqual(
                    link["target_relative"], "src/theory/Payload.sml",
                )
                tampered = copy.deepcopy(inventory)
                tampered_link = next(
                    entry for entry in tampered["sigobj_entries"]
                    if entry["kind"] == "symlink"
                )
                tampered_link["target_relative"] = "generated.sml"
                tampered_link["target_path"] = str(root / "generated.sml")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "role/target contract mismatch",
                ):
                    subject.validate_hol_proof_artifact_inventory(
                        tampered, root, require_live=False,
                    )
                payload.write_bytes(b"changed")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "inventory changed",
                ):
                    subject.validate_hol_proof_artifact_inventory(
                        inventory, root, require_live=True,
                    )

    def test_hol_proof_artifact_inventory_rejects_external_sigobj_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            outside = root.parent / f"{root.name}-outside"
            outside.write_bytes(b"outside")
            try:
                (root / "sigobj").mkdir()
                (root / "sigobj/escape").symlink_to(outside)
                with mock.patch.object(
                    subject, "HOL_PROOF_OBJECT_COUNT", 0,
                ), mock.patch.object(
                    subject, "HOL_SIGOBJ_ORDINARY_COUNT", 0,
                ), mock.patch.object(
                    subject, "HOL_SIGOBJ_SYMLINK_COUNT", 1,
                ), mock.patch.object(
                    subject, "HOL_GENERATED_PROOF_INPUTS", (),
                ), mock.patch.object(
                    subject, "HOL_PROOF_OBJECT_PATHS_SHA256",
                    subject._canonical_json_sha256([]),
                ):
                    with self.assertRaisesRegex(
                        subject.ProvenanceError, "target escapes",
                    ):
                        subject.hol_proof_artifact_inventory(root)
            finally:
                outside.unlink(missing_ok=True)

    def test_make_dependency_inventory_binds_depfiles_and_lastmakers(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            hol_root = root / "hol"
            cakeml_root = root / "cakeml"
            hol_deps = hol_root / "one/.hol/make-deps"
            cake_deps = cakeml_root / "ancestor/.hol/make-deps"
            hol_deps.mkdir(parents=True)
            cake_deps.mkdir(parents=True)
            expected_lastmaker = subject.bootstrap_lastmaker_bytes(hol_root)
            (hol_deps / "lastmaker").write_bytes(expected_lastmaker)
            (cake_deps / "lastmaker").write_bytes(expected_lastmaker)
            hol_depfile = hol_deps / "FooScript.sml.d"
            hol_depfile.write_bytes(b"hol dependency")
            (cake_deps / "AncestorScript.sml.d").write_bytes(
                b"cakeml dependency",
            )
            hol_paths = [
                "one/.hol/make-deps/FooScript.sml.d",
                "one/.hol/make-deps/lastmaker",
            ]
            cake_paths = [
                "ancestor/.hol/make-deps/AncestorScript.sml.d",
                "ancestor/.hol/make-deps/lastmaker",
            ]
            with mock.patch.object(
                subject, "HOL_MAKE_DEPENDENCY_COUNT", 2,
            ), mock.patch.object(
                subject, "CAKEML_MAKE_DEPENDENCY_ANCESTOR_COUNT", 2,
            ), mock.patch.object(
                subject, "HOL_MAKE_DEPENDENCY_PATHS_SHA256",
                subject._canonical_json_sha256(hol_paths),
            ), mock.patch.object(
                subject, "CAKEML_MAKE_DEPENDENCY_ANCESTOR_PATHS_SHA256",
                subject._canonical_json_sha256(cake_paths),
            ):
                inventory = subject.bootstrap_make_dependency_artifact_inventory(
                    cakeml_root, hol_root,
                )
                subject.validate_bootstrap_make_dependency_artifact_inventory(
                    inventory, cakeml_root, hol_root, require_live=True,
                )
                alternate = copy.deepcopy(inventory)
                retained_lastmaker = next(
                    entry for entry in alternate["cakeml_ancestor_entries"]
                    if Path(entry["relative"]).name == "lastmaker"
                )
                retained_lastmaker["identity"].update(
                    subject.bytes_record(b"/bin/true\n"),
                )
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "does not name pinned Holmake",
                ):
                    subject.validate_bootstrap_make_dependency_artifact_inventory(
                        alternate, cakeml_root, hol_root, require_live=False,
                    )
                wrong_path = copy.deepcopy(inventory)
                wrong_path_entry = wrong_path["hol_entries"][0]
                wrong_path_entry["relative"] = (
                    "one/.hol/make-deps/AAAInjected.sml.d"
                )
                wrong_path_entry["path"] = str(
                    hol_root / wrong_path_entry["relative"]
                )
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "path set mismatch",
                ):
                    subject.validate_bootstrap_make_dependency_artifact_inventory(
                        wrong_path, cakeml_root, hol_root, require_live=False,
                    )
                hol_depfile.write_bytes(b"malicious dependency")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "inventory changed",
                ):
                    subject.validate_bootstrap_make_dependency_artifact_inventory(
                        inventory, cakeml_root, hol_root, require_live=True,
                    )

    def test_make_dependency_inventory_rejects_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            hol_root = root / "hol"
            cakeml_root = root / "cakeml"
            deps = hol_root / "one/.hol/make-deps"
            deps.mkdir(parents=True)
            cakeml_root.mkdir()
            target = hol_root / "target"
            target.write_bytes(b"dependency")
            (deps / "Injected.d").symlink_to(target)
            with self.assertRaisesRegex(
                subject.ProvenanceError,
                "symlink inside make-dependency inventory",
            ):
                subject.bootstrap_make_dependency_artifact_inventory(
                    cakeml_root, hol_root,
                )

    def test_cake_compile_heap_record_rejects_drift(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            heap = root / subject.CAKE_COMPILE_HEAP_RELATIVE
            heap.parent.mkdir(parents=True)
            heap.write_bytes(b"saved compiler heap")
            holmakefile = (
                root / subject.CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE
            )
            holmakefile.parent.mkdir(parents=True)
            holmakefile.write_text(
                "ifdef POLY\nHOLHEAP = $(CAKEMLDIR)/cv_translator/"
                "cake_compile_heap\nendif\n",
                encoding="utf-8",
            )
            subprocess.run(
                ["/usr/bin/git", "init", "-q"], cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            subprocess.run(
                ["/usr/bin/git", "add",
                 subject.CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE],
                cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            subprocess.run(
                ["/usr/bin/git", "-c", "user.name=Test", "-c",
                 "user.email=test@example.invalid", "commit", "-qm", "heap"],
                cwd=root, check=True,
                env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            )
            record = subject.cake_compile_heap_record(root)
            subject.validate_cake_compile_heap_record(
                record, root, require_live=True,
            )
            heap.write_bytes(b"replacement heap")
            with self.assertRaisesRegex(
                subject.ProvenanceError, "compile heap changed",
            ):
                subject.validate_cake_compile_heap_record(
                    record, root, require_live=True,
                )
            heap.unlink()
            target = root / "replacement-heap"
            target.write_bytes(b"saved compiler heap")
            heap.symlink_to(target)
            with self.assertRaisesRegex(
                subject.ProvenanceError, "capture ordinary file",
            ):
                subject.validate_cake_compile_heap_record(
                    record, root, require_live=True,
                )

    def test_obsolete_manual_bootstrap_phases_are_not_public_commands(self) -> None:
        script = Path(subject.__file__).resolve()
        for command in (
            "record-bootstrap-preflight", "prepare-bootstrap",
            "bootstrap-log-preamble", "record-bootstrap",
        ):
            with self.subTest(command=command):
                result = subprocess.run(
                    ["/usr/bin/python3", "-I", "-S", str(script), command],
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    text=True,
                    env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
                )
                self.assertEqual(result.returncode, 2)
                self.assertIn("invalid choice", result.stdout)

    def test_controller_rejects_injected_outer_environment(self) -> None:
        controller = (
            Path(subject.__file__).resolve().parent.parent /
            "build-local-cakeml-bootstrap.sh"
        )
        result = subprocess.run(
            [str(controller), "/missing/cakeml", "/missing/hol",
             "/tmp/missing.log", "/tmp/missing-preflight.json",
             "/tmp/missing-final.json"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            env={
                "LC_ALL": "C", "PATH": "/usr/bin:/bin",
                "LD_LIBRARY_PATH": "/injected",
            },
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unexpected controller launch environment", result.stdout)

    def test_run_bootstrap_nonzero_never_calls_final_recorder(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "attempt.log"
            preflight = root / "preflight.json"
            final = root / "final.json"
            fake = {
                "launch": {
                    "cwd": str(root),
                    "environment": {
                        "PATH": "/usr/bin:/bin", "LC_ALL": "C",
                        "HOLDIR": str(root),
                    },
                    "time_argv": ["/usr/bin/time", "-v", "/bin/false"],
                    "timed_argv": ["/bin/false"],
                    "build_command": "/bin/false",
                    "log_path": str(log),
                },
            }
            def prepare_before_log(*_arguments):
                self.assertFalse(log.exists())

            with mock.patch.object(
                subject, "bootstrap_controller_environment",
                return_value={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            ), mock.patch.object(
                subject, "record_bootstrap_preflight", return_value=fake,
            ), mock.patch.object(
                subject, "prepare_bootstrap_output",
                side_effect=prepare_before_log,
            ), mock.patch.object(subject, "record_bootstrap") as final_recorder:
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "exited with status 1",
                ):
                    subject.run_bootstrap(
                        root, root, root, log, preflight, final,
                    )
            final_recorder.assert_not_called()
            self.assertTrue(log.is_file())
            self.assertFalse(final.exists())

    def test_hol_runtime_record_pins_launchers_state_and_closures(self) -> None:
        original_tags = subject.HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS
        try:
            subject.HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS = {}
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "bin").mkdir()
                shutil.copyfile("/bin/true", root / "bin/Holmake")
                shutil.copyfile("/bin/true", root / "bin/hol")
                (root / "bin/hol.state").write_bytes(b"saved-state")
                (root / ".kernelidstr").write_bytes(b"stdknl\n")
                record = subject.hol_runtime_record(root)
                subject.validate_hol_runtime_record(record, hol_root=root)
                wrong_kernel = copy.deepcopy(record)
                wrong_kernel["files"][".kernelidstr"] = subject.bytes_record(
                    b"injected-kernel\n",
                )
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "kernel identifier mismatch",
                ):
                    subject.validate_hol_runtime_record(wrong_kernel)
                (root / "bin/hol.state").write_bytes(b"tampered")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "provenance mismatch",
                ):
                    subject.validate_hol_runtime_record(record, hol_root=root)
                (root / "bin/hol.state").write_bytes(b"saved-state")
                (root / ".kernelidstr").write_bytes(b"injected-kernel\n")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "provenance mismatch",
                ):
                    subject.validate_hol_runtime_record(record, hol_root=root)
        finally:
            subject.HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS = original_tags

    def test_bootstrap_host_runtime_binds_requested_bin_sh_and_closure(self) -> None:
        record = subject.bootstrap_host_runtime_record()
        subject.validate_bootstrap_host_runtime_record(
            record, require_live=True,
        )
        shell = record["tools"]["sh"]
        self.assertEqual(shell["requested_path"], "/bin/sh")
        self.assertEqual(shell["symlink_target"], "dash")
        self.assertEqual(shell["resolved_path"], "/bin/dash")
        self.assertIn("sh", record["launch_elf_closures"])

    def test_runtime_environment_rejects_loader_controls(self) -> None:
        for variable in ("LD_PRELOAD", "LD_AUDIT", "LD_LIBRARY_PATH",
                         "GLIBC_TUNABLES"):
            with self.subTest(variable=variable):
                with self.assertRaisesRegex(
                    subject.ProvenanceError,
                    "forbidden dynamic-loader environment",
                ):
                    subject.runtime_environment({variable: "injected"})

    def test_runtime_environment_fixes_locale(self) -> None:
        self.assertEqual(
            subject.runtime_environment({"LANG": "de_DE.UTF-8"})["LC_ALL"],
            "C",
        )

    def test_runtime_environment_allows_only_decimal_cakeml_sizes(self) -> None:
        environment = subject.runtime_environment({
            "CML_HEAP_SIZE": "6000",
            "CML_STACK_SIZE": "512",
            "HOME": "/not-forwarded",
        })
        self.assertEqual(environment, {
            "CML_HEAP_SIZE": "6000",
            "CML_STACK_SIZE": "512",
            "LC_ALL": "C",
            "PATH": "/usr/bin:/bin",
        })
        with self.assertRaisesRegex(
            subject.ProvenanceError, "invalid CakeML runtime size",
        ):
            subject.runtime_environment({"CML_HEAP_SIZE": "6G"})

    def test_root_runtime_aliases_are_exact_relative_links(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            build = root / "candle/build"
            build.mkdir(parents=True)
            outputs = {}
            for name in subject.ROOT_RUNTIME_ALIASES:
                target = build / name
                target.write_text(name, encoding="utf-8")
                outputs[name] = subject.file_record(target)
                (root / name).symlink_to(Path("candle/build") / name)
            subject.validate_root_runtime_aliases(root, outputs)
            alias = root / subject.ROOT_RUNTIME_ALIASES[0]
            alias.unlink()
            alias.symlink_to(build / subject.ROOT_RUNTIME_ALIASES[0])
            with self.assertRaisesRegex(
                subject.ProvenanceError, "alias target mismatch",
            ):
                subject.validate_root_runtime_aliases(root, outputs)

    def test_provenance_inputs_reject_symlinks_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            target = root / "target"
            target.write_bytes(b"authenticated bytes")
            alias = root / "alias"
            alias.symlink_to(target)
            with self.assertRaisesRegex(
                subject.ProvenanceError, "ordinary provenance input",
            ):
                subject.file_record(alias)
            self.assertEqual(
                subject.file_record(alias, allow_symlink=True),
                subject.file_record(target),
            )

    def test_cake_patch_derivation_replays_exact_postimage(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            preimage = root / "cake.S.bootstrap"
            postimage = root / "cake.S"
            patch = root / "cake.S.patch"
            preimage.write_text("old\n", encoding="utf-8")
            postimage.write_text("new\n", encoding="utf-8")
            patch.write_text(
                "--- cake.S\n+++ cake.S\n@@ -1 +1 @@\n-old\n+new\n",
                encoding="utf-8",
            )
            derivation = subject.cake_patch_derivation(
                root, subject.file_record(preimage), patch,
            )
            self.assertEqual(
                derivation["policy"],
                "gnu_patch_exact_preimage_and_postimage_v1",
            )
            postimage.write_text("tampered\n", encoding="utf-8")
            with self.assertRaisesRegex(
                subject.ProvenanceError, "postimage mismatch",
            ):
                subject.cake_patch_derivation(
                    root, subject.file_record(preimage), patch,
                )

    def test_native_link_derivation_relinks_and_binds_exact_commands(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            build_small_installed_elf(build)
            record = subject.native_link_derivation(build)
            subject.validate_native_link_derivation(build, record)
            self.assertEqual(
                record["candidate_elf"], record["installed_elf"],
            )
            self.assertEqual(len(record["commands"]["as"]), 2)
            self.assertEqual(len(record["commands"]["ld"]), 1)
            tampered = copy.deepcopy(record)
            tampered["commands"]["ld"][0].append("--injected")
            with self.assertRaisesRegex(
                subject.ProvenanceError, "collect2 link plan",
            ):
                subject.validate_native_link_derivation(build, tampered)

    def test_native_link_derivation_rejects_nonmatching_installed_elf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            build_small_installed_elf(build)
            (build / "cake").write_bytes(b"\x7fELFnot-the-relinked-program")
            with self.assertRaisesRegex(
                subject.ProvenanceError, "not byte-identical",
            ):
                subject.native_link_derivation(build)

    def test_native_link_validation_rejects_forged_replacement_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            build_small_installed_elf(build)
            record = subject.native_link_derivation(build)
            shutil.copyfile("/bin/true", build / "cake")
            # Simulate the old false-green: update the self-certified live
            # output identities while retaining the authenticated inputs.
            replacement = subject.file_record(build / "cake")
            record["candidate_elf"] = replacement
            record["installed_elf"] = replacement
            with self.assertRaisesRegex(
                subject.ProvenanceError,
                "not byte-identical|fresh native link derivation differs",
            ):
                subject.validate_native_link_derivation(build, record)

    def test_native_link_validation_rejects_environment_and_tool_tampering(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            build_small_installed_elf(build)
            record = subject.native_link_derivation(build)
            tampered_environment = copy.deepcopy(record)
            tampered_environment["environment"]["PATH"] = "/injected"
            with self.assertRaisesRegex(
                subject.ProvenanceError, "environment mismatch",
            ):
                subject.validate_native_link_derivation(
                    build, tampered_environment,
                )
            tampered_tool = copy.deepcopy(record)
            tampered_tool["toolchain"]["tools"]["cc"]["file"]["sha256"] = (
                "0" * 64
            )
            with self.assertRaisesRegex(
                subject.ProvenanceError, "host toolchain mismatch",
            ):
                subject.validate_native_link_derivation(build, tampered_tool)

    def test_linked_bootstrap_copy_rejects_self_recorded_wrong_kind(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            preflight = build / subject.LINKED_BOOTSTRAP_PREFLIGHT
            preflight.write_text("{}\n", encoding="utf-8")
            log = build / subject.LINKED_BOOTSTRAP_LOG
            log.write_text("retained log\n", encoding="utf-8")
            pins = {
                "cakeml_commit": "c" * 40,
                "hol4_commit": "h" * 40,
                "manifest_sha256": "m" * 64,
            }
            durable = {
                "schema": subject.BOOTSTRAP_PROVENANCE_SCHEMA,
                "kind": "self-recorded-wrong-kind",
                **pins,
                "candle_commit": "d" * 40,
                "candle_root": "/build/candle",
                "cakeml_root": "/build/cakeml",
                "hol4_root": "/build/hol4",
                "build_command": "/build/hol4/bin/Holmake -j1 cake.S",
                "preflight": {
                    "path": subject.LINKED_BOOTSTRAP_PREFLIGHT,
                    **subject.file_record(preflight),
                },
                "bootstrap_log": {
                    "path": subject.LINKED_BOOTSTRAP_LOG,
                    **subject.file_record(log),
                },
                "inputs": {},
                "host_runtime": {},
                "hol_runtime": {},
                "python_controller": {},
                "controller_environment": {},
                "forced_output_transitions": [],
                "preserved_symlink_input_transitions": {},
                "source_bootstrap_record": {"bytes": 1, "sha256": "0" * 64},
            }
            record_path = build / subject.LINKED_BOOTSTRAP_RECORD
            record_path.write_text(json.dumps(durable), encoding="utf-8")
            linked = {
                **pins,
                "cakeml_commit": pins["cakeml_commit"],
                "hol4_commit": pins["hol4_commit"],
                "bootstrap_record": subject.file_record(record_path),
                "bootstrap_preflight": subject.file_record(preflight),
                "bootstrap_log": subject.file_record(log),
            }
            with self.assertRaisesRegex(
                subject.ProvenanceError, "bootstrap provenance kind",
            ):
                subject.validate_linked_bootstrap_copy(build, linked, pins)

    def test_candle_elf_policy_rejects_extra_object(self) -> None:
        closure = {
            "policy": "ldd_roles_resolved_absolute_paths_and_content_v3",
            "dynamic_path_tags": {},
            "files": {
                f"/runtime/{name}": {"bytes": 1, "sha256": "0" * 64}
                for name in subject.CANDLE_ELF_OBJECTS
            },
            "roles": {
                name: f"/runtime/{name}"
                for name in subject.CANDLE_ELF_OBJECTS
            },
            "virtual_objects": list(subject.CANDLE_ELF_VIRTUAL_OBJECTS),
        }
        subject.validate_candle_elf_policy(closure)
        closure["files"]["/runtime/libinjected.so"] = {
            "bytes": 1, "sha256": "1" * 64,
        }
        with self.assertRaisesRegex(
            subject.ProvenanceError, "dependency object count",
        ):
            subject.validate_candle_elf_policy(closure)

    def test_candle_elf_policy_rejects_duplicate_basename_extra_object(self) -> None:
        closure = {
            "policy": "ldd_roles_resolved_absolute_paths_and_content_v3",
            "dynamic_path_tags": {},
            "files": {
                f"/runtime/{name}": {"bytes": 1, "sha256": "0" * 64}
                for name in subject.CANDLE_ELF_OBJECTS
            },
            "roles": {
                name: f"/runtime/{name}"
                for name in subject.CANDLE_ELF_OBJECTS
            },
            "virtual_objects": list(subject.CANDLE_ELF_VIRTUAL_OBJECTS),
        }
        closure["files"]["/injected/libc.so.6"] = {
            "bytes": 1, "sha256": "1" * 64,
        }
        with self.assertRaisesRegex(
            subject.ProvenanceError, "dependency object count",
        ):
            subject.validate_candle_elf_policy(closure)


if __name__ == "__main__":
    unittest.main()
