#!/usr/bin/env python3

import unittest

import test_float_literals as subject


class FloatLiteralGateTests(unittest.TestCase):
    def test_runtime_boundaries_check_conversion_and_literal_exception(self):
        payload = subject._load_cases()
        source = subject._candle_positive_source(payload)
        for case in payload["runtime_divergence_cases"]:
            with self.subTest(case=case["id"]):
                self.assertIn(
                    f'Double.fromString "{case["literal"]}"', source,
                )
                self.assertIn(
                    f'candle_float_{case["id"]}_fromstring_none', source,
                )
                self.assertIn(
                    f'candle_float_{case["id"]}_raises', source,
                )

    def test_success_marker_is_last_declaration(self):
        source = subject._candle_positive_source(subject._load_cases())
        self.assertTrue(source.endswith(
            "let candle_float_differential_passed = true;;\n"
        ))


if __name__ == "__main__":
    unittest.main()
