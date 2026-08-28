#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cakeml_artifact_provenance as subject


class CakeMLArtifactProvenanceTests(unittest.TestCase):
    def test_manifest_pins_exact_dopen_stack(self) -> None:
        candle_root = Path(__file__).resolve().parent.parent
        pins = subject.expected_pins(candle_root)
        self.assertEqual(
            pins["cakeml_commit"],
            "0c170aa374ec178e5db8a9fe9276244ed7e0dcf7",
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
            "ldd_resolved_absolute_paths_and_content_v1",
        )
        self.assertTrue(closure["files"])
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

    def test_candle_elf_policy_rejects_extra_object(self) -> None:
        closure = {
            "files": {
                f"/runtime/{name}": {"bytes": 1, "sha256": "0" * 64}
                for name in subject.CANDLE_ELF_OBJECTS
            },
            "virtual_objects": list(subject.CANDLE_ELF_VIRTUAL_OBJECTS),
        }
        subject.validate_candle_elf_policy(closure)
        closure["files"]["/runtime/libinjected.so"] = {
            "bytes": 1, "sha256": "1" * 64,
        }
        with self.assertRaisesRegex(
            subject.ProvenanceError, "unexpected.*dependency roles",
        ):
            subject.validate_candle_elf_policy(closure)


if __name__ == "__main__":
    unittest.main()
