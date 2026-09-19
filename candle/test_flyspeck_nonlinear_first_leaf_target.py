#!/usr/bin/env python3

import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
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
        self.assertEqual(
            oracle["legacy_theorem_digest"],
            "f7ff5f16bf03b6885aa4d46bb1490001",
        )

    def test_oracle_is_explicitly_non_release(self) -> None:
        self.assertEqual(self.payload["status"], "development-non-release")
        self.assertIn("no Candle proof", self.payload["claim"])


if __name__ == "__main__":
    unittest.main()
