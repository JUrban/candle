#!/usr/bin/env python3
"""Static tests for the compiled direct-corpus decimal-float gate."""

import collections
import inspect
import json
from pathlib import Path
import sys
import tempfile
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

    def test_evidence_path_is_ocaml_escaped(self):
        self.assertEqual(
            checker._ocaml_string('/tmp/a "quoted" path'),
            '"/tmp/a \\"quoted\\" path"',
        )
        with self.assertRaises(corpus.CorpusError):
            checker._ocaml_string("/tmp/newline\npath")

    def test_evidence_archive_binds_bytes_and_rejects_symlink_source(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            source.write_bytes(b"authenticated")
            expected = corpus.file_record(source)
            destination = root / "evidence/archive"
            observed = checker._archive_file(source, destination, expected)
            self.assertEqual(observed, expected)
            alias = root / "alias"
            alias.symlink_to(source)
            with self.assertRaises(corpus.CorpusError):
                checker._archive_file(alias, root / "rejected")

    def test_archived_artifact_is_cross_bound_to_executed_payload(self):
        source = inspect.getsource(checker.check_candle)
        self.assertIn("expected_artifact_bytes", source)
        self.assertIn("artifact_archive.read_bytes()", source)
        self.assertIn("== payload", source)

    def test_compiled_runner_requires_independent_completeness_gate(self):
        implementation = Path(checker.__file__).read_text(encoding="utf-8")
        self.assertIn(
            "check_flyspeck_float_completeness.validate_completeness(",
            implementation,
        )


if __name__ == "__main__":
    unittest.main()
