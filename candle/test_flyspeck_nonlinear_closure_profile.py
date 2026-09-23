#!/usr/bin/env python3

import copy
import hashlib
import unittest
from pathlib import Path

import flyspeck_nonlinear_closure_profile as profile
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
FLYSPECK = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)


class NonlinearClosureProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        _, _, cls.records = smoke.authenticate_closure(ROOT, FLYSPECK)

    def test_exact_taylor_instrumentation(self) -> None:
        records = copy.deepcopy(self.records)
        receipt = profile.instrument_records(records)
        self.assertEqual(receipt["operation_count"], 32)
        self.assertEqual(len(receipt["section_events"]), 28)
        record = next(
            item for item in records if item["source_key"] == profile.SOURCE_KEY
        )
        data = record["normalized_bytes"]
        text = data.decode("ascii")
        self.assertEqual(
            receipt["normalized_sha256"], hashlib.sha256(data).hexdigest(),
        )
        self.assertEqual(record["normalization"]["id"], profile.NORMALIZATION_ID)
        self.assertEqual(text.count(profile.MARKER_PREFIX), 32)
        self.assertIn("stage=module-frontend event=begin", text)
        self.assertIn("stage=module-execution event=begin", text)
        self.assertIn("stage=module-execution event=end", text)
        self.assertIn("stage=module-frontend event=end", text)
        self.assertIn("stage=section section=NthDerivatives event=begin", text)
        self.assertIn("stage=section section=TaylorArith event=end", text)

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
