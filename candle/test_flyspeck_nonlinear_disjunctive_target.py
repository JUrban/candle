#!/usr/bin/env python3

import json
import sys
import unittest
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_disjunctive_target as subject


class NonlinearDisjunctiveTargetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_target(FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_target_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_target_is_minimum_retained_family_member(self) -> None:
        target = self.payload["target"]
        oracle = self.payload["native_oracle"]
        self.assertEqual(target["id"], "prep-8293089898")
        self.assertEqual(target["global_case"], 16479)
        self.assertEqual(target["local_case"], 149)
        self.assertEqual(
            target["selection"],
            "minimum formal leaf count in retained family",
        )
        self.assertIn("frac_right 5 #0.5000", target["legacy_ineqm_text"])
        self.assertEqual(oracle["formal_leaf_count"], 788)
        self.assertEqual(oracle["formal_raw_leaf_count"], 0)
        self.assertEqual(oracle["formal_mono_count"], 0)
        self.assertEqual(oracle["formal_glue_count"], 787)
        self.assertEqual(oracle["formal_convex_glue_count"], 0)
        self.assertEqual(oracle["formal_pass_mono_count"], 0)
        self.assertEqual(oracle["total_seconds"], 561.614339)
        self.assertEqual(
            oracle["legacy_theorem_digest"],
            "0b95a6345d43bd6aa35e3892f2c38bf9",
        )

    def test_family_context_is_complete_and_ordinary(self) -> None:
        family = self.payload["family"]
        self.assertEqual(family["member_count"], 333)
        self.assertEqual(family["global_case_first"], 16330)
        self.assertEqual(family["global_case_last"], 16662)
        self.assertEqual(family["formal_leaf_count"], 2787684)
        self.assertEqual(family["formal_glue_count"], 2787351)
        self.assertEqual(
            family["historical_total_seconds"], "2153899.320383",
        )
        self.assertTrue(family["ordinary_only"])
        self.assertEqual(
            family["archive_tree"]["top_action"],
            {"kind": "Iarg_bisect", "coordinate": 4},
        )

    def test_target_is_non_release_and_source_authenticated(self) -> None:
        self.assertEqual(self.payload["status"], "development-non-release")
        self.assertIn("no Candle proof", self.payload["claim"])
        self.assertEqual(
            self.payload["flyspeck_commit"],
            "d6cdcd9f3e45f4ceb5fd1ba08f5b5ec4ce6a65eb",
        )
        evidence = self.payload["evidence_files"]
        self.assertEqual(len(evidence), 16)
        for record in evidence.values():
            self.assertGreater(record["bytes"], 0)
            self.assertEqual(len(record["sha256"]), 64)

    def test_wrong_repository_identity_fails_closed(self) -> None:
        with mock.patch.object(
            subject.common, "_git_head", return_value="0" * 40,
        ):
            with self.assertRaisesRegex(ValueError, "differs from closure"):
                subject.build_target(FLYSPECK_ROOT)

    def test_changed_evidence_bytes_fail_closed(self) -> None:
        relative = subject.AZURE_STDOUT
        with mock.patch.object(
            subject.common,
            "_identity",
            return_value={
                "logical_relative_path": relative.as_posix(),
                "bytes": 1,
                "sha256": "0" * 64,
            },
        ):
            with self.assertRaisesRegex(ValueError, "evidence drifted"):
                subject._verified_identity(FLYSPECK_ROOT, relative)


if __name__ == "__main__":
    unittest.main()
