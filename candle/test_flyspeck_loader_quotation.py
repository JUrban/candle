#!/usr/bin/env python3

import hashlib
import importlib.util
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SPEC = importlib.util.spec_from_file_location(
    "flyspeck_loader_quotation", HERE / "flyspeck_loader_quotation.py",
)
subject = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(subject)
CAKEML_ROOT = Path(
    "/project/worktrees/cakeml-flyspeck-frontend-cold-8a8926906-v13"
)


class LoaderQuotationTests(unittest.TestCase):
    def test_exact_quotexpander_cases_and_string_escaping(self) -> None:
        cases = {
            b"x = y": (b'parse_term "x = y"', "term"),
            b":num->bool": (b'parse_type "num->bool"', "type"),
            b";proof": (b'parse_qproof ";proof"', "qproof"),
            b"name:": (b'"name"', "string"),
            b'a\\b\t\n"c': (b'parse_term "a\\\\b\\t\\n\\"c"', "term"),
        }
        for body, expected in cases.items():
            with self.subTest(body=body):
                self.assertEqual(subject.expand_body(body), expected)
        with self.assertRaisesRegex(subject.QuotationError, "empty"):
            subject.expand_body(b"")

    def test_expands_only_loader_visible_backticks(self) -> None:
        source = (
            b"(* outer `comment` (* nested `comment` *) *)\n"
            b'let s = "`string`" and c = \'`\' in `x = "y"`;;\n'
            b"let ty = `:A->bool` and q = `;proof` and n = `name:`;;\n"
        )
        expanded, record = subject.expand_source(source)
        self.assertIn(b"`comment`", expanded)
        self.assertIn(b'"`string`"', expanded)
        self.assertIn(b"'`'", expanded)
        self.assertIn(b'(parse_term "x = \\"y\\"")', expanded)
        self.assertIn(b'(parse_type "A->bool")', expanded)
        self.assertIn(b'(parse_qproof ";proof")', expanded)
        self.assertIn(b'("name")', expanded)
        self.assertEqual(record["quotation_count"], 4)
        self.assertEqual(
            record["kind_counts"],
            {"term": 1, "type": 1, "qproof": 1, "string": 1},
        )
        self.assertEqual(record["input_sha256"], hashlib.sha256(source).hexdigest())
        self.assertEqual(record["output_sha256"], hashlib.sha256(expanded).hexdigest())

    def test_rejects_lexically_unclosed_inputs(self) -> None:
        cases = (b"`x", b"(* x", b'"x', b"'\\x")
        for source in cases:
            with self.subTest(source=source), self.assertRaises(subject.QuotationError):
                subject.expand_source(source)

    def test_contract_matches_pinned_runtime_sources(self) -> None:
        contract = subject.contract()
        boot = CAKEML_ROOT / contract["cakeml_loader"]["path"]
        system = ROOT / contract["candle_quotexpander"]["path"]
        self.assertEqual(
            hashlib.sha256(boot.read_bytes()).hexdigest(),
            contract["cakeml_loader"]["sha256"],
        )
        self.assertEqual(
            hashlib.sha256(system.read_bytes()).hexdigest(),
            contract["candle_quotexpander"]["sha256"],
        )

    def test_three_raw_pilot_failures_are_rewritten(self) -> None:
        cases = (
            b'override_interface ("<=>",`(=):bool->bool->bool`);;\n',
            b"let andtm = `(/\\)` in\n",
            b"let _FALSITY_ = new_definition `_FALSITY_ = F`;;\n",
        )
        for source in cases:
            with self.subTest(source=source):
                expanded, record = subject.expand_source(source)
                self.assertNotIn(b"`", expanded)
                self.assertEqual(record["quotation_count"], 1)
                self.assertIn(b"parse_term", expanded)


if __name__ == "__main__":
    unittest.main()
