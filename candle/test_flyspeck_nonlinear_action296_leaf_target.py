#!/usr/bin/env python3

import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_action296_leaf_target as subject


class NonlinearAction296LeafTargetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_target(FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_target_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_target_pins_real_action296_workload(self) -> None:
        target = self.payload["target"]
        oracle = self.payload["native_oracle"]
        self.assertEqual(target["id"], "prep-8657368829")
        self.assertEqual(target["global_case"], 10172)
        self.assertEqual(target["local_case"], 0)
        self.assertIn("frac_right 0 #0.5000", target["legacy_ineqm_text"])
        self.assertEqual(oracle["formal_leaf_count"], 1061)
        self.assertEqual(oracle["formal_raw_leaf_count"], 0)
        self.assertEqual(oracle["formal_mono_count"], 0)
        self.assertEqual(oracle["formal_glue_count"], 1060)
        self.assertEqual(oracle["formal_convex_glue_count"], 0)
        self.assertEqual(oracle["formal_pass_mono_count"], 0)
        self.assertEqual(oracle["total_seconds"], 667.725002)
        self.assertEqual(
            oracle["legacy_theorem_digest"],
            "9e11e82fc40c91d58cdf811a429ffdd5",
        )

    def test_target_is_non_release_and_source_authenticated(self) -> None:
        self.assertEqual(self.payload["status"], "development-non-release")
        self.assertIn("no Candle proof", self.payload["claim"])
        evidence = self.payload["evidence_files"]
        self.assertEqual(len(evidence), 7)
        for record in evidence.values():
            self.assertGreater(record["bytes"], 0)
            self.assertEqual(len(record["sha256"]), 64)


if __name__ == "__main__":
    unittest.main()
