#!/usr/bin/env python3

import hashlib
import json
import sys
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_first_leaf as subject
import flyspeck_nonlinear_verifier_smoke as smoke


class NonlinearFirstLeafRunnerTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.closure_data, _, cls.closure_records = smoke.authenticate_closure(
            ROOT, FLYSPECK_ROOT,
        )
        cls.target_data, cls.target, cls.support_records = (
            subject.authenticate_target(FLYSPECK_ROOT, cls.closure_data)
        )
        cls.driver = subject.build_target_driver(
            cls.target, FLYSPECK_ROOT, cls.support_records,
        )
        cls.profile_driver = subject.build_target_driver(
            cls.target, FLYSPECK_ROOT, cls.support_records, True,
        )

    def test_exact_support_is_wrapped_and_authenticated(self) -> None:
        self.assertEqual(len(self.support_records), 3)
        self.assertEqual(
            {record["normalization"]["module"]
             for record in self.support_records
             if record["normalization"] is not None},
            {"Definitions", "Break_case"},
        )
        for record in self.support_records:
            normalized = record["normalized_bytes"]
            normalization = record["normalization"]
            if normalization is None:
                self.assertEqual(
                    normalized,
                    Path(record["physical_path"]).read_bytes(),
                )
            else:
                self.assertEqual(
                    hashlib.sha256(normalized).hexdigest(),
                    normalization["normalized_sha256"],
                )
        definitions = next(
            record["normalized_bytes"] for record in self.support_records
            if record["normalization"] is not None
            and record["normalization"]["module"] == "Definitions"
        )
        break_case = next(
            record["normalized_bytes"] for record in self.support_records
            if record["normalization"] is not None
            and record["normalization"]["module"] == "Break_case"
        )
        self.assertIn(b"open Prove_by_refinement;;", definitions)
        self.assertIn(b"open Prove_by_refinement\n", break_case)
        self.assertIn(b"open Definitions\n", break_case)

    def test_driver_requires_exact_ordinary_theorem(self) -> None:
        self.assertIn(
            self.target["target"]["legacy_ineqm_text"], self.driver,
        )
        self.assertIn("Break_case.ineqm_conv", self.driver)
        self.assertIn("M_verifier_main.verify_ineq", self.driver)
        self.assertIn("first-leaf support loader identity did not commit", self.driver)
        self.assertIn("hyp candle_nonlinear_first_leaf_theorem <> []", self.driver)
        self.assertIn(
            "concl candle_nonlinear_first_leaf_theorem <>", self.driver,
        )
        self.assertIn(subject.PASS_MARKER, self.driver)
        self.assertIn(subject.FORMAL_VERIFICATION_SECONDS, self.driver)
        self.assertNotIn("Printf.sprintf", self.driver)
        self.assertIn("string_of_float", self.driver)
        self.assertNotIn("candle_nonlinear_profile_marker", self.driver)

    def test_profile_driver_brackets_the_exact_verifier_call(self) -> None:
        begin = (
            'candle_nonlinear_profile_marker "target" "total" "begin";;'
        )
        end = 'candle_nonlinear_profile_marker "target" "total" "end";;'
        call = "M_verifier_main.verify_ineq"
        self.assertEqual(self.profile_driver.count(begin), 1)
        self.assertEqual(self.profile_driver.count(end), 1)
        self.assertLess(self.profile_driver.index(begin), self.profile_driver.index(call))
        self.assertLess(self.profile_driver.index(call), self.profile_driver.index(end))

    def test_result_timing_parser_is_fail_closed(self) -> None:
        marker = subject.RECONSTRUCTION_SECONDS
        self.assertEqual(
            subject._extract_seconds(f"{marker} 1.250000\n".encode(), marker),
            1.25,
        )
        self.assertEqual(
            subject._extract_seconds(f"{marker} 1.25e+02\n".encode(), marker),
            125.0,
        )
        self.assertEqual(
            subject._extract_seconds(f"{marker} 0.\n".encode(), marker),
            0.0,
        )
        self.assertIsNone(subject._extract_seconds(b"", marker))
        duplicate = f"{marker} 1.0\n{marker} 2.0\n".encode()
        self.assertIsNone(subject._extract_seconds(duplicate, marker))


if __name__ == "__main__":
    unittest.main()
