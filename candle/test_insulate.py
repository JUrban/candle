#!/usr/bin/env python3
"""Unit checks for the generated CakeML API insulation layer."""

import unittest

import insulate


class InsulateTests(unittest.TestCase):
    def test_only_decimal_parser_runtime_functions_survive_stubbing(self):
        bindings = {
            "Double": [
                {"func_name": "fromString", "param_count": 1},
                {"func_name": "toString", "param_count": 1},
            ],
            "Option": [
                {"func_name": "map", "param_count": 2},
                {"func_name": "valOf", "param_count": 1},
            ],
        }

        output = insulate.generate_ocaml_bindings(bindings)
        stubs = output.split("(* Module stubs", 1)[1]

        self.assertIn(
            "let fromString x0 = Cake.Double.fromString x0", stubs)
        self.assertIn("let valOf x0 = Cake.Option.valOf x0", stubs)
        self.assertNotIn("let toString", stubs)
        self.assertNotIn("let map", stubs)

    def test_missing_parser_runtime_function_fails_closed(self):
        bindings = {
            "Double": [{"func_name": "fromString", "param_count": 1}],
            "Option": [{"func_name": "map", "param_count": 2}],
        }

        with self.assertRaisesRegex(ValueError, "Option.valOf"):
            insulate.generate_ocaml_bindings(bindings)

    def test_missing_parser_runtime_module_fails_closed(self):
        bindings = {
            "Double": [{"func_name": "fromString", "param_count": 1}],
        }

        with self.assertRaisesRegex(ValueError, "missing Option module"):
            insulate.generate_ocaml_bindings(bindings)

    def test_parser_runtime_arity_drift_fails_closed(self):
        bindings = {
            "Double": [{"func_name": "fromString", "param_count": 2}],
            "Option": [{"func_name": "valOf", "param_count": 1}],
        }

        with self.assertRaisesRegex(ValueError, "unexpected arity"):
            insulate.generate_ocaml_bindings(bindings)


if __name__ == "__main__":
    unittest.main()
