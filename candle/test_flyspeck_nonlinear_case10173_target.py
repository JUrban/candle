#!/usr/bin/env python3

import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_case10173_target as subject


class NonlinearCase10173TargetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_target(FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_target_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_target_pins_real_shared_expression_sibling(self) -> None:
        target = self.payload["target"]
        oracle = self.payload["native_oracle"]
        self.assertEqual(target["id"], "prep-8657368829")
        self.assertEqual(target["global_case"], 10173)
        self.assertEqual(target["local_case"], 1)
        self.assertIn("frac_left 0 #0.5000", target["legacy_ineqm_text"])
        self.assertEqual(target["first_tree_action"]["side"], "left")
        self.assertEqual(oracle["formal_leaf_count"], 3305)
        self.assertEqual(oracle["formal_raw_leaf_count"], 0)
        self.assertEqual(oracle["formal_mono_count"], 0)
        self.assertEqual(oracle["formal_glue_count"], 3304)
        self.assertEqual(oracle["formal_convex_glue_count"], 0)
        self.assertEqual(oracle["formal_pass_mono_count"], 0)
        self.assertEqual(oracle["total_seconds"], 2084.239248)
        self.assertEqual(
            oracle["legacy_theorem_digest"],
            "5d721da6d2d9cc50128448bb9b9bd24f",
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
