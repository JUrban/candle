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

import flyspeck_nonlinear_first_leaf_target as subject


class NonlinearFirstLeafTargetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_target(FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_target_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_substantial_native_target_is_exact(self) -> None:
        target = self.payload["target"]
        oracle = self.payload["native_oracle"]
        self.assertEqual(target["global_case"], 7853)
        self.assertEqual(target["local_case"], 0)
        self.assertEqual(
            target["public_bounds"][0]["upper"],
            {"numerator": 36218753, "denominator": 6250000,
             "decimal": "5.79500048"},
        )
        self.assertEqual(oracle["precision"], 6)
        self.assertEqual(oracle["epsilon"], "1e-10")
        self.assertEqual(oracle["total_seconds"], 365.672506)
        self.assertEqual(oracle["formal_leaf_count"], 16)
        self.assertEqual(oracle["formal_raw_leaf_count"], 0)
        self.assertEqual(oracle["formal_mono_count"], 0)
        self.assertEqual(oracle["formal_glue_count"], 15)
        self.assertEqual(oracle["formal_convex_glue_count"], 0)
        self.assertEqual(oracle["formal_pass_mono_count"], 0)
        self.assertEqual(
            oracle["legacy_theorem_digest"],
            "f7ff5f16bf03b6885aa4d46bb1490001",
        )

    def test_oracle_is_explicitly_non_release(self) -> None:
        self.assertEqual(self.payload["status"], "development-non-release")
        self.assertIn("no Candle proof", self.payload["claim"])

    def test_reconstruction_support_is_authenticated(self) -> None:
        evidence = self.payload["evidence_files"]
        self.assertEqual(set(evidence), {
            "azure_stdout",
            "break_case_log",
            "prep",
            "main_verifier",
            "prove_by_refinement",
            "compiled_definitions",
            "compiled_break_case",
        })
        for record in evidence.values():
            self.assertGreater(record["bytes"], 0)
            self.assertEqual(len(record["sha256"]), 64)


if __name__ == "__main__":
    unittest.main()
