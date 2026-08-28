#!/usr/bin/env python3
"""Focused tests for the independent OCaml-lexer completeness check."""

from pathlib import Path
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import check_flyspeck_float_completeness as subject
import flyspeck_float_corpus


class IndependentFloatCompletenessTests(unittest.TestCase):
    def oracle(self, source: bytes):
        with tempfile.TemporaryDirectory(
            prefix="independent-float-fixture-"
        ) as tmp:
            path = Path(tmp) / "fixture.ml"
            path.write_bytes(source)
            return subject.oracle_sites([{
                "key": "fixture:test.ml",
                "runtime_path": path,
            }], "/usr/bin/ocamlc")

    def test_ocaml_lexer_owns_context_and_numeric_classification(self):
        observed = self.oracle(
            b"let decimal = 2.;;\n"
            b"(* comment 3.0 (* nested 4.0 *) *)\n"
            b'let text = "string 5.0 and escaped \\\" 6.0";;\n'
            b"let character = '7';;\n"
            b"let identifier2 = 0;; identifier2.0;;\n"
            b"let exponent = 1e3 +. 1.0e-8 +. 3_000e+37;;\n"
            b"let term = `#9.0 + #10.0`;;\n"
            b"let hexadecimal = 0x1.0p0;;\n"
        )
        self.assertEqual(
            [site["literal"] for site in observed],
            ["2.", "1e3", "1.0e-8", "3_000e+37", "0x1.0p0"],
        )
        self.assertEqual(
            [(site["line"], site["column"]) for site in observed],
            [(1, 15), (6, 16), (6, 23), (6, 33), (8, 19)],
        )

    def test_nonfloat_integer_lexer_error_recovers_without_losing_float(self):
        observed = self.oracle(b"let x = 0in let y = 11.9999;;\n")
        self.assertEqual([site["literal"] for site in observed], ["11.9999"])

    def test_float_suffix_fails_closed(self):
        with self.assertRaisesRegex(
            flyspeck_float_corpus.CorpusError,
            "float suffix|potential float literal",
        ):
            self.oracle(b"let bad = 2.0foo;;\n")

    def test_malformed_exponents_fail_closed(self):
        for literal in (b"1e", b"1e+", b"1e--2"):
            with self.subTest(literal=literal):
                with self.assertRaisesRegex(
                    flyspeck_float_corpus.CorpusError,
                    "potential float literal",
                ):
                    self.oracle(b"let bad = " + literal + b";;\n")

    def test_unterminated_hol_quotation_fails_closed(self):
        with self.assertRaisesRegex(
            flyspeck_float_corpus.CorpusError,
            "unterminated HOL backtick quotation",
        ):
            self.oracle(b"let term = `#2.0 + #3.0;;\n")

    def test_completeness_checker_does_not_call_python_token_scanner(self):
        implementation = Path(subject.__file__).read_text(encoding="utf-8")
        self.assertNotIn("scan_source(", implementation)
        self.assertNotIn("scan_corpus(", implementation)
        oracle = subject.ORACLE_SOURCE.read_text(encoding="utf-8")
        self.assertIn("Lexer.token", oracle)
        self.assertIn("Parser.FLOAT", oracle)


if __name__ == "__main__":
    unittest.main()
