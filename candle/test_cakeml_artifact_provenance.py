#!/usr/bin/env python3

import json
import shutil
import tempfile
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cakeml_artifact_provenance as subject


def successful_bootstrap_log(build_command: str) -> str:
    lines = [
        "Writing cv to file: cake.S",
        'Exporting theory "x64Bootstrap" ... done.',
        "Holmake: [18/18] x64Bootstrap",
    ]
    for label in subject.GNU_TIME_FOOTER_LABELS:
        if label == "Command being timed":
            value = f'"{build_command}"'
        elif label == "Exit status":
            value = "0"
        else:
            value = "0"
        lines.append(f"\t{label}: {value}")
    return "\n".join(lines) + "\n"


class CakeMLArtifactProvenanceTests(unittest.TestCase):
    def test_manifest_pins_exact_dopen_stack(self) -> None:
        candle_root = Path(__file__).resolve().parent.parent
        pins = subject.expected_pins(candle_root)
        self.assertEqual(
            pins["cakeml_commit"],
            "36e2245f42d4759063615c97fec51865798ca894",
        )
        self.assertEqual(
            pins["hol4_commit"],
            "a390cbabd3a4521bab4ee20281e3e42933a8a3ae",
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
                record = subject.hol_runtime_record(root)
                subject.validate_hol_runtime_record(record, hol_root=root)
                (root / "bin/hol.state").write_bytes(b"tampered")
                with self.assertRaisesRegex(
                    subject.ProvenanceError, "provenance mismatch",
                ):
                    subject.validate_hol_runtime_record(record, hol_root=root)
        finally:
            subject.HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS = original_tags

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

    def test_linked_bootstrap_copy_rejects_self_recorded_wrong_kind(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            build = Path(directory)
            inputs = {}
            for name in subject.BOOTSTRAP_INPUTS:
                local_name = "cake.S.bootstrap" if name == "cake.S" else name
                path = build / local_name
                path.write_text(name, encoding="utf-8")
                inputs[name] = subject.file_record(path)
            log = build / subject.LINKED_BOOTSTRAP_LOG
            build_command = (
                "env HOLDIR=/build/hol4 /build/hol4/bin/Holmake -j1 cake.S"
            )
            log.write_text(
                successful_bootstrap_log(build_command),
                encoding="utf-8",
            )
            pins = {
                "cakeml_commit": "c" * 40,
                "hol4_commit": "h" * 40,
                "manifest_sha256": "m" * 64,
            }
            durable = {
                "schema": 2,
                "kind": "candle-linked-bootstrap-provenance-copy",
                **pins,
                "cakeml_root": "/build/cakeml",
                "hol4_root": "/build/hol4",
                "build_command": build_command,
                "bootstrap_log": {
                    "path": subject.LINKED_BOOTSTRAP_LOG,
                    **subject.file_record(log),
                },
                "inputs": inputs,
                "hol_runtime": {
                    "policy": "exact_hol_launchers_state_and_elf_closure_v1",
                    "files": {
                        name: {"bytes": 1, "sha256": "0" * 64}
                        for name in subject.HOL_BOOTSTRAP_RUNTIME_FILES
                    },
                    "elf_closures": {
                        name: {
                            "policy":
                                "ldd_roles_resolved_absolute_paths_and_content_v3",
                            "dynamic_path_tags":
                                subject.HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS,
                            "files": {
                                "/lib/runtime.so": {
                                    "bytes": 1, "sha256": "0" * 64,
                                },
                            },
                            "roles": {"runtime.so": "/lib/runtime.so"},
                            "virtual_objects": [],
                        }
                        for name in subject.HOL_BOOTSTRAP_ELF_FILES
                    },
                },
                "source_bootstrap_record": {"bytes": 1, "sha256": "0" * 64},
            }
            record_path = build / subject.LINKED_BOOTSTRAP_RECORD
            record_path.write_text(json.dumps(durable), encoding="utf-8")
            linked = {
                **pins,
                "bootstrap_record": subject.file_record(record_path),
                "bootstrap_log": subject.file_record(log),
            }
            subject.validate_linked_bootstrap_copy(build, linked, pins)
            durable["kind"] = "self-recorded-wrong-kind"
            record_path.write_text(json.dumps(durable), encoding="utf-8")
            linked["bootstrap_record"] = subject.file_record(record_path)
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
