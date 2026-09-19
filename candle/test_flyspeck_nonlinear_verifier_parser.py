#!/usr/bin/env python3

import copy
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_verifier_parser as subject


class NonlinearVerifierParserReuseTest(unittest.TestCase):
    def setUp(self) -> None:
        self.base = {
            "index": 7,
            "source": {
                "repository": "flyspeck",
                "logical_relative_path": "formal_ineqs/example.hl",
                "bytes": 12,
                "md5": "1" * 32,
                "sha256": "2" * 64,
            },
            "manifest_action_count": 3,
            "quotation_expansion": {"output_sha256": "3" * 64},
            "prepared_input": {"bytes": 20, "sha256": "4" * 64},
        }
        self.prior = {
            **copy.deepcopy(self.base),
            "outcome": "parse-ok",
            "exit_code": 0,
            "stderr": {"bytes": 0, "sha256": "5" * 64},
        }

    def test_exact_success_is_reusable(self) -> None:
        self.assertTrue(subject._can_reuse_prior_attempt(
            self.base, self.prior, None,
        ))

    def test_normalized_source_is_never_reused(self) -> None:
        self.assertFalse(subject._can_reuse_prior_attempt(
            self.base, self.prior, {"id": "normalization"},
        ))

    def test_prepared_input_drift_is_rejected(self) -> None:
        changed = copy.deepcopy(self.prior)
        changed["prepared_input"]["sha256"] = "6" * 64
        self.assertFalse(subject._can_reuse_prior_attempt(
            self.base, changed, None,
        ))

    def test_failure_and_stderr_are_rejected(self) -> None:
        for field, value in (
            ("outcome", "parse-error"),
            ("exit_code", 65),
        ):
            changed = copy.deepcopy(self.prior)
            changed[field] = value
            self.assertFalse(subject._can_reuse_prior_attempt(
                self.base, changed, None,
            ))
        changed = copy.deepcopy(self.prior)
        changed["stderr"]["bytes"] = 1
        self.assertFalse(subject._can_reuse_prior_attempt(
            self.base, changed, None,
        ))


if __name__ == "__main__":
    unittest.main()
