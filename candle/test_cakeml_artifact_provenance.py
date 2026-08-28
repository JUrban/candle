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


if __name__ == "__main__":
    unittest.main()
