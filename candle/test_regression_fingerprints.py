#!/usr/bin/env python3
"""Deterministic tests for S1 fingerprint request/report plumbing."""

import hashlib
from pathlib import Path
import tempfile
import unittest

import regression


class FingerprintPlumbingTest(unittest.TestCase):
    def test_request_source_accepts_only_binding_names(self):
        self.assertEqual(
            regression._fingerprint_request_source(("THM", "theorem'")),
            ('candle_s1_emit_fingerprint "THM" THM;;\n'
             'candle_s1_emit_fingerprint "theorem\'" theorem\';;\n'))
        with self.assertRaises(ValueError):
            regression._fingerprint_request_source(("THM; failwith",))

    def test_structural_records_become_compact_hashes(self):
        fields = [
            regression.FINGERPRINT_MARKER,
            "THM",
            "theorem-serialization",
            "hypothesis-serialization",
            "conclusion-serialization",
            "axiom-serialization",
            "2",
            "3",
        ]
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("ordinary Candle output\n")
            logfile.write("\t".join(fields) + "\n")
            path = Path(logfile.name)
        try:
            report = regression._read_fingerprint_records(
                path, ("THM",), "audited")
        finally:
            path.unlink()

        self.assertEqual(report["status"], "observed_uncompared")
        self.assertFalse(report["expected_identities_present"])
        record = report["theorems"][0]
        self.assertEqual(record["hypothesis_count"], 2)
        self.assertEqual(record["global_axiom_count"], 3)
        self.assertEqual(
            record["theorem_sha256"],
            hashlib.sha256(b"theorem-serialization").hexdigest())

    def test_missing_record_is_not_a_load_success_fingerprint(self):
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("target loaded, but emitted no identity\n")
            path = Path(logfile.name)
        try:
            with self.assertRaises(regression.LoadFailure):
                regression._read_fingerprint_records(
                    path, ("MISSING",), "audited")
        finally:
            path.unlink()


if __name__ == "__main__":
    unittest.main()
