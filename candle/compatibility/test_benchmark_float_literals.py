#!/usr/bin/env python3
"""Static tests for the representative decimal-float load benchmark."""

import unittest

import benchmark_float_literals


class FloatBenchmarkSourceTest(unittest.TestCase):
    def test_each_scenario_has_the_requested_number_of_terms(self):
        for scenario, expression in (
                benchmark_float_literals.SCENARIO_EXPRESSIONS.items()):
            source = benchmark_float_literals._source(scenario, 3)
            self.assertEqual(source.count(expression), 3)
            self.assertTrue(source.endswith("];;\n"))

    def test_aggregate_does_not_hide_mixed_results(self):
        result = benchmark_float_literals._aggregate([
            {"outcome": "pass", "elapsed_seconds": 1.0},
            {"outcome": "reject", "elapsed_seconds": 2.0},
        ])
        self.assertEqual(result["outcome"], "mixed")
        self.assertEqual(result["median_seconds"], 1.5)


if __name__ == "__main__":
    unittest.main()
