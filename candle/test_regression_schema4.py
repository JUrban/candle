#!/usr/bin/env python3
"""Static and adversarial tests for the promotable Great 100 schema-4 gate."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import regression


class Great100Schema4Test(unittest.TestCase):
    def _transcript(self, suite, process, linked, fingerprint_inside=True):
        fingerprint = "\t".join([
            regression.FINGERPRINT_MARKER, b"T".hex(), b"t".hex(),
            b"h".hex(), b"c".hex(), b"a".hex(), "0", "3"])
        state = "\t".join([
            regression.STATE_FINGERPRINT_MARKER, b"s".hex(), b"y".hex(),
            b"c".hex(), b"d".hex(), b"a".hex(), "1", "2", "3", "3"])
        lines = [
            f"{regression.SUITE_MARKER}\t{suite}",
            f"{regression.PROCESS_MARKER}\t{suite}\t{process}\tSTART",
            f"{regression.LINKED_RECORD_MARKER}\t{linked}",
        ]
        if fingerprint_inside:
            lines.extend([fingerprint, state])
        lines.append(
            f"{regression.PROCESS_MARKER}\t{suite}\t{process}\tCOMPLETE")
        if not fingerprint_inside:
            lines.extend([fingerprint, state])
        return "\n".join(lines) + "\n"

    def test_marker_order_and_exact_linked_observation(self):
        suite, process, linked = "1" * 64, "2" * 64, "3" * 64
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as stream:
            stream.write(self._transcript(suite, process, linked))
            path = Path(stream.name)
        try:
            self.assertEqual(
                regression._read_process_markers(path, suite, process, linked),
                {"suite_line": 0, "start_line": 1, "linked_line": 2,
                 "complete_line": 5})
            with self.assertRaisesRegex(regression.LoadFailure, "linked marker"):
                regression._read_process_markers(
                    path, suite, process, "4" * 64)
        finally:
            path.unlink()

    def test_fingerprint_outside_process_interval_fails(self):
        suite, process, linked = "1" * 64, "2" * 64, "3" * 64
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as stream:
            stream.write(self._transcript(
                suite, process, linked, fingerprint_inside=False))
            path = Path(stream.name)
        try:
            with self.assertRaisesRegex(regression.LoadFailure, "outside"):
                regression._read_process_markers(path, suite, process, linked)
        finally:
            path.unlink()

    def test_completion_marker_is_nonce_bound(self):
        suite, process = "a" * 64, "b" * 64
        source = regression._fingerprint_request_source(
            ("EGCD",), suite, process)
        self.assertIn(
            f"{regression.PROCESS_MARKER}\\t{suite}\\t{process}\\tCOMPLETE",
            source)
        with self.assertRaisesRegex(ValueError, "nonce"):
            regression._fingerprint_request_source(("EGCD",), suite, "bad")

    def test_manifest_source_closure_is_exact_65_66_97(self):
        manifest = json.loads((
            regression.CANDLE_ROOT / "candle/top100_manifest.json"
        ).read_text(encoding="utf-8"))
        closure = regression._source_closure(manifest)
        self.assertEqual(
            (closure["target_count"], closure["source_file_count"],
             closure["fingerprint_request_count"]), (65, 66, 97))
        digest_input = dict(closure)
        del digest_input["sha256"]
        self.assertEqual(closure["sha256"],
                         regression._canonical_digest(digest_input))

    def test_runtime_state_rejects_any_contract_mutation(self):
        base = {
            "candle_git_head": "0" * 40, "candle_git_status": [],
            "execution_contract": {}, "execution_contract_sha256": "1" * 64,
            "source_closure": {"sha256": "2" * 64},
            "independent_approval": {"sha256": "3" * 64},
            "linked_record": {"sha256": "4" * 64},
            "candle_executable": {"sha256": "5" * 64},
        }
        changed = json.loads(json.dumps(base))
        changed["execution_contract_sha256"] = "6" * 64
        with mock.patch.object(
                regression, "_capture_suite_contract", return_value=changed):
            with self.assertRaisesRegex(ValueError, "execution_contract"):
                regression._runtime_state(base)

    def test_shell_emits_all_authenticated_startup_markers(self):
        source = (regression.CANDLE_ROOT / "candle.sh").read_text(encoding="utf-8")
        self.assertIn("CANDLE_GREAT100_SUITE_V1\\t%s", source)
        self.assertIn("CANDLE_GREAT100_PROCESS_V1\\t%s\\t%s\\tSTART", source)
        self.assertIn("CANDLE_LINKED_PROVENANCE_V1\\t%s", source)
        self.assertLess(source.index("CANDLE_GREAT100_SUITE_V1"),
                        source.index("check-linked"))
        self.assertLess(source.index("check-linked"),
                        source.index("CANDLE_LINKED_PROVENANCE_V1"))

    def test_ordinary_file_record_rejects_symlink(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target"
            target.write_bytes(b"evidence")
            link = root / "link"
            link.symlink_to(target)
            with self.assertRaisesRegex(ValueError, "ordinary file"):
                regression._ordinary_file_record(link)
            record = regression._ordinary_file_record(target)
            self.assertEqual(record["bytes"], 8)
            self.assertEqual(record["sha256"], hashlib.sha256(b"evidence").hexdigest())


if __name__ == "__main__":
    unittest.main()
