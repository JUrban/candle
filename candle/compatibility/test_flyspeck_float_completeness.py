#!/usr/bin/env python3
"""Focused tests for the independent OCaml-lexer completeness check."""

from pathlib import Path
import stat
import sys
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import check_flyspeck_float_completeness as subject
import flyspeck_float_corpus


class IndependentFloatCompletenessTests(unittest.TestCase):
    def observation(self, source: bytes):
        with tempfile.TemporaryDirectory(
            prefix="independent-float-fixture-"
        ) as tmp:
            path = Path(tmp) / "fixture.ml"
            path.write_bytes(source)
            return subject.oracle_observation([{
                "key": "fixture:test.ml",
                "runtime_path": path,
            }], "/usr/bin/ocamlc")

    def oracle(self, source: bytes):
        sites, _toolchain, _quotations = self.observation(source)
        return sites

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
            self.oracle(b"let term = `#2.0 + #3.0\n")

    def test_paired_polymorphic_variants_cannot_hide_later_float(self):
        with self.assertRaisesRegex(
            flyspeck_float_corpus.CorpusError,
            "ambiguous paired backticks",
        ):
            self.oracle(b"let a = `Foo;; let x = 2.0;; let b = `Bar;;\n")

    def test_variant_tuple_is_outside_selected_backtick_dialect(self):
        sites, _toolchain, quotations = self.observation(
            b"let pair = (`Foo 2.0, `Bar);;\n"
        )
        self.assertEqual(sites, [])
        self.assertEqual(len(quotations), 1)
        with self.assertRaisesRegex(
            flyspeck_float_corpus.CorpusError,
            "backtick dialect contract mismatch",
        ):
            subject.selected_quotation_dialect(quotations)

    def test_completeness_checker_does_not_call_python_token_scanner(self):
        implementation = Path(subject.__file__).read_text(encoding="utf-8")
        self.assertNotIn("scan_source(", implementation)
        self.assertNotIn("scan_corpus(", implementation)
        self.assertIn("postflight independent runtime snapshot", implementation)
        self.assertIn("toolchain changed during independent", implementation)
        oracle = subject.ORACLE_SOURCE.read_text(encoding="utf-8")
        self.assertIn("Lexer.token", oracle)
        self.assertIn("Parser.FLOAT", oracle)

    def test_runtime_snapshot_is_byte_exact_and_read_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source.hl"
            output = root / "snapshot"
            source.write_bytes(b"let x = 2.0;;\n")
            output.mkdir()
            source_record = flyspeck_float_corpus.file_record(source)
            snapshots = subject.snapshot_runtime_sources([{
                "key": "fixture:source.hl",
                "runtime_path": source,
                "runtime_sha256": source_record["sha256"],
            }], output)
            retained = snapshots[0]["runtime_path"]
            self.assertEqual(retained.read_bytes(), source.read_bytes())
            self.assertEqual(snapshots[0]["runtime_snapshot"], source_record)
            self.assertEqual(stat.S_IMODE(retained.stat().st_mode), 0o444)

    def test_ocaml_lexer_toolchain_is_exactly_pinned(self):
        observed = subject.validate_toolchain("/usr/bin/ocamlc")
        self.assertEqual(observed["ocaml_version"], "4.14.1")
        self.assertEqual(set(observed["files"]),
                         set(subject.EXPECTED_TOOLCHAIN))
        for label, expected in subject.EXPECTED_TOOLCHAIN.items():
            with self.subTest(label=label):
                self.assertEqual(observed["files"][label], expected)

    def test_compiled_oracle_bytecode_is_reproducibly_pinned(self):
        with tempfile.TemporaryDirectory() as temporary:
            executable = subject.compile_oracle(
                "/usr/bin/ocamlc", Path(temporary)
            )
            self.assertEqual(
                flyspeck_float_corpus.file_record(executable),
                subject.EXPECTED_COMPILED_ORACLE,
            )
            for name, expected in subject.EXPECTED_COMPILED_OBJECTS.items():
                self.assertEqual(
                    flyspeck_float_corpus.file_record(
                        Path(temporary) / name
                    ),
                    expected,
                )


if __name__ == "__main__":
    unittest.main()
