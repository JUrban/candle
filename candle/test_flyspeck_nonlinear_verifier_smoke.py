#!/usr/bin/env python3

import json
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_verifier_smoke as subject


class NonlinearVerifierSmokeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.closure_data, cls.closure, cls.records = (
            subject.authenticate_closure(ROOT, FLYSPECK_ROOT)
        )
        cls.temp = tempfile.TemporaryDirectory()
        cls.overlays = subject.materialize_normalizations(
            Path(cls.temp.name), cls.records,
        )
        cls.driver = subject.build_driver(
            ROOT, FLYSPECK_ROOT, cls.records, cls.overlays,
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls.temp.cleanup()

    def test_authenticates_the_published_complete_closure(self) -> None:
        self.assertEqual(len(self.records), 90)
        self.assertEqual(
            self.closure,
            json.loads(self.closure_data),
        )
        self.assertEqual(
            {record["repository"] for record in self.records},
            {"candle", "flyspeck"},
        )
        self.assertEqual(len(self.overlays), 4)

    def test_every_identity_is_in_the_runtime_preflight(self) -> None:
        for record in self.records:
            self.assertIn(record["physical_path"], self.driver)
            self.assertIn(record["md5"], self.driver)
        self.assertEqual(
            self.driver.count("nonlinear verifier source digest mismatch"),
            1,
        )

    def test_arithmetic_base_precedes_verifier_load_and_proof(self) -> None:
        options = self.driver.index('needs "arith_options.hl";;')
        base = self.driver.index("Arith_options.base := 200;;")
        verifier = self.driver.index('needs "verifier/m_verifier_main.hl";;')
        proof = self.driver.index("verify_ineq")
        success = self.driver.index(subject.PASS_MARKER)
        self.assertLess(options, base)
        self.assertLess(base, verifier)
        self.assertLess(verifier, proof)
        self.assertLess(proof, success)
        self.assertIn(subject.CLOSURE_SECONDS, self.driver)
        self.assertIn(subject.SMOKE_PROOF_SECONDS, self.driver)

    def test_gate_requires_exact_theorem_interface_and_axiom_stability(self) -> None:
        self.assertIn("hyp candle_nonlinear_smoke_theorem <> []", self.driver)
        self.assertIn(
            "concl candle_nonlinear_smoke_theorem <> "
            "candle_nonlinear_smoke_term",
            self.driver,
        )
        self.assertIn("candle_nonlinear_axioms_before", self.driver)
        self.assertIn("candle_nonlinear_axioms_after", self.driver)

    def test_absolute_driver_keeps_unprefixed_resolver_entry(self) -> None:
        stdin = subject.build_stdin(
            ROOT, Path("/tmp/support"), Path("/tmp/run/driver.ml"),
        )
        self.assertIn("Filename.currentDir", stdin)
        self.assertIn('#use "/tmp/run/driver.ml";;', stdin)


if __name__ == "__main__":
    unittest.main()
