#!/usr/bin/env python3
"""Static tests for the compiled direct-corpus decimal-float gate."""

import collections
import hashlib
import inspect
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


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
        self.assertIn("snapshot_runtime_sources(", implementation)
        self.assertIn("independent_ocaml_toolchain", implementation)
        self.assertIn("independent_oracle_binary", implementation)
        self.assertIn("independent_oracle_compile_outputs", implementation)
        self.assertIn("independent_python_sources", implementation)
        self.assertIn(
            '"execution_binding": python_runtime["execution_binding"]',
            implementation,
        )
        self.assertIn(
            "check_flyspeck_float_completeness.compile_oracle(",
            implementation,
        )

    def test_local_python_evidence_set_is_exact(self):
        completeness_sources = {
            label: {
                "path": str(path),
                **corpus.file_record(path),
            }
            for label, path in (
                checker.check_flyspeck_float_completeness
                .PYTHON_SOURCE_PATHS.items()
            )
        }
        observed = checker.local_python_source_records({
            "python_sources": completeness_sources,
        })
        self.assertEqual(set(observed), {
            "cakeml_artifact_provenance.py",
            "check_flyspeck_float_completeness.py",
            "check_flyspeck_float_corpus.py",
            "flyspeck_float_corpus.py",
            "runtime_lock.py",
        })
        for module in (
            checker.cakeml_artifact_provenance,
            checker.check_flyspeck_float_completeness,
            checker.flyspeck_float_corpus,
            checker.runtime_lock,
        ):
            self.assertEqual(
                module.__candle_source_sha256__,
                hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest(),
            )

    def test_executed_local_source_divergence_is_rejected(self):
        completeness_sources = {
            label: {
                "path": str(path),
                **corpus.file_record(path),
            }
            for label, path in (
                checker.check_flyspeck_float_completeness
                .PYTHON_SOURCE_PATHS.items()
            )
        }
        module = checker.runtime_lock
        original = module.__candle_source_bytes__
        module.__candle_source_bytes__ = original + b"\n# mutation\n"
        try:
            with self.assertRaisesRegex(
                corpus.CorpusError,
                "executed local Python source identity mismatch",
            ):
                checker.local_python_source_records({
                    "python_sources": completeness_sources,
                })
        finally:
            module.__candle_source_bytes__ = original

    def test_python_and_pexpect_execution_sources_are_pinned(self):
        script = f"""
import sys
import tempfile
from pathlib import Path
sys.path.insert(0, {str(HERE)!r})
import check_flyspeck_float_corpus as c
assert c.validate_python_runtime() == c.EXPECTED_PYTHON_RUNTIME
with tempfile.TemporaryDirectory() as temporary:
    p, sources = c.load_pexpect_from_pinned_sources(
        Path(temporary) / "sources"
    )
    for name, expected in c.EXPECTED_PEXPECT_SOURCES.items():
        assert {{field: sources[name][field] for field in ("bytes", "sha256")}} == {{
            field: expected[field] for field in ("bytes", "sha256")
        }}
print('PINNED_PYTHON_PEXPECT_PASS')
"""
        completed = subprocess.run(
            ["/usr/bin/python3", "-I", "-c", script], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        )
        self.assertEqual(completed.stdout.strip(),
                         "PINNED_PYTHON_PEXPECT_PASS")

    def test_system_wide_loader_preload_is_rejected(self):
        with mock.patch.object(
            checker.cakeml_artifact_provenance.os.path, "lexists",
            return_value=True,
        ):
            with self.assertRaisesRegex(
                checker.cakeml_artifact_provenance.ProvenanceError,
                "system-wide dynamic-loader preload",
            ):
                checker.cakeml_artifact_provenance.runtime_environment()


if __name__ == "__main__":
    unittest.main()
