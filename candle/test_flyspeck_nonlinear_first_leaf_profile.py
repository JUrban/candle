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
        record = next(
            item for item in records if item["source_key"] == profile.SOURCE_KEY
        )
        data = record["normalized_bytes"]
        self.assertEqual(
            receipt["normalized_sha256"], hashlib.sha256(data).hexdigest()
        )
        self.assertEqual(record["normalization"]["id"], profile.NORMALIZATION_ID)
        text = data.decode("utf-8")
        self.assertEqual(text.count(profile.MARKER_PREFIX), 1)
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

    def test_identity_drift_fails_closed(self) -> None:
        records = copy.deepcopy(self.records)
        record = next(
            item for item in records if item["source_key"] == profile.SOURCE_KEY
        )
        record["normalized_bytes"] += b"\n"
        with self.assertRaisesRegex(ValueError, "identity drift"):
            profile.instrument_records(records)


if __name__ == "__main__":
    unittest.main()
