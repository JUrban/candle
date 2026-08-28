#!/usr/bin/env python3
"""Static tests for the compiled direct-corpus decimal-float gate."""

import collections
import json
from pathlib import Path
import sys
import unittest


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import check_flyspeck_float_corpus as checker
import flyspeck_float_corpus as corpus


class CompiledFlyspeckFloatCorpusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.payload = json.loads(
            (HERE / "flyspeck_float_corpus.json").read_text(encoding="utf-8")
        )

    def test_generated_source_evaluates_every_exact_spelling_once(self):
        source = checker.candle_source(self.payload)
        checker.validate_generated_source(self.payload, source)
        observed = corpus.scan_source("generated:corpus.ml",
                                      source.encode("ascii"))
        self.assertEqual(
            collections.Counter(site["literal"] for site in observed["sites"]),
            collections.Counter({record["literal"]: 1
                                 for record in self.payload["spellings"]}),
        )

    def test_generated_source_is_bounded_and_has_final_witness(self):
        source = checker.candle_source(self.payload)
        expected_chunks = (
            len(self.payload["spellings"]) + checker.CHUNK_SIZE - 1
        ) // checker.CHUNK_SIZE
        self.assertEqual(source.count(
            "let candle_flyspeck_float_chunk_"), expected_chunks)
        self.assertTrue(source.endswith(
            "let candle_flyspeck_float_corpus_passed = true;;\n"
        ))
        self.assertIn(
            f"candle_flyspeck_float_checked = {len(self.payload['spellings'])}",
            source,
        )

    def test_invalid_chunk_size_fails_closed(self):
        with self.assertRaises(corpus.CorpusError):
            checker.candle_source(self.payload, chunk_size=0)

    def test_word_mutation_changes_generated_gate(self):
        original = checker.candle_source(self.payload)
        mutated = json.loads(json.dumps(self.payload))
        mutated["spellings"][0]["ocaml_word64_decimal"] = "1"
        self.assertNotEqual(checker.candle_source(mutated), original)

    def test_compiled_runner_requires_independent_completeness_gate(self):
        implementation = Path(checker.__file__).read_text(encoding="utf-8")
        self.assertIn(
            "check_flyspeck_float_completeness.validate_completeness(",
            implementation,
        )


if __name__ == "__main__":
    unittest.main()
