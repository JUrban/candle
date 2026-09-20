#!/usr/bin/env python3

import copy
import hashlib
import unittest
from pathlib import Path

import flyspeck_nonlinear_first_leaf_profile as profile
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
FLYSPECK = Path("/project/worktrees/flyspeck-v13-source")


class NonlinearFirstLeafProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        _, _, cls.records = smoke.authenticate_closure(ROOT, FLYSPECK)

    def test_exact_phase_instrumentation(self) -> None:
        records = copy.deepcopy(self.records)
        receipt = profile.instrument_records(records)
        self.assertEqual(receipt["source_count"], 2)
        by_key = {item["source_key"]: item for item in receipt["sources"]}
        main_record = next(
            item for item in records
            if item["source_key"] == profile.MAIN_SOURCE_KEY
        )
        formal_record = next(
            item for item in records
            if item["source_key"] == profile.FORMAL_SOURCE_KEY
        )
        for record in (main_record, formal_record):
            data = record["normalized_bytes"]
            self.assertEqual(
                by_key[record["source_key"]]["normalized_sha256"],
                hashlib.sha256(data).hexdigest(),
            )
            self.assertEqual(
                record["normalization"]["id"], profile.NORMALIZATION_ID,
            )
            self.assertEqual(
                data.decode("utf-8").count(profile.MARKER_PREFIX), 1,
            )
        text = main_record["normalized_bytes"].decode("utf-8")
        for phase in (
            "standardize",
            "problem-reification",
            "evaluator-build",
            "informal-search",
            "adaptive-informal-verification",
            "formal-verification",
            "final-normalization",
        ):
            self.assertIn(f'"{phase}" "begin"', text)
            self.assertIn(f'"{phase}" "end"', text)
        formal_text = formal_record["normalized_bytes"].decode("utf-8")
        for phase in ("leaf-check", "domain-split", "theorem-glue"):
            self.assertIn(f'"{phase}" "begin"', formal_text)
            self.assertIn(f'"{phase}" "end"', formal_text)
        self.assertIn('"formal-leaf-" ^ string_of_int !k', formal_text)
        self.assertIn('"formal-glue-" ^ string_of_int !glue_k', formal_text)

    def test_identity_drift_fails_closed(self) -> None:
        records = copy.deepcopy(self.records)
        for source_key in (profile.MAIN_SOURCE_KEY, profile.FORMAL_SOURCE_KEY):
            drifted = copy.deepcopy(records)
            record = next(
                item for item in drifted if item["source_key"] == source_key
            )
            record["normalized_bytes"] += b"\n"
            with self.subTest(source_key=source_key):
                with self.assertRaisesRegex(ValueError, "identity drift"):
                    profile.instrument_records(drifted)


if __name__ == "__main__":
    unittest.main()
