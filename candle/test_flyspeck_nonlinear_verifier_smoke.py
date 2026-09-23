#!/usr/bin/env python3

import json
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)
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
        cls.big_int_compatibility, cls.big_int_record = (
            subject.authenticate_big_int_compatibility(ROOT)
        )
        cls.driver = subject.build_driver(
            ROOT, FLYSPECK_ROOT, cls.records, cls.overlays,
            cls.big_int_compatibility,
        )
        cls.closure_driver = subject.build_driver(
            ROOT, FLYSPECK_ROOT, cls.records, cls.overlays,
            cls.big_int_compatibility, closure_only=True,
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
        self.assertEqual(len(self.overlays), 28)

    def test_central_big_int_overlay_is_complete_and_source_bound(self) -> None:
        self.assertEqual(
            set(self.big_int_record["float_constants"]["overlay_members"]),
            subject.FLOAT_CONSTANT_MEMBERS,
        )
        self.assertEqual(
            set(self.big_int_record["assert_helper"]["overlay_members"]),
            subject.ASSERT_HELPER_MEMBERS,
        )
        self.assertIn("Assert_failure", self.big_int_compatibility)
        self.assertEqual(
            set(self.big_int_record["float_constants"][
                "closure_selected_members"
            ]),
            subject.FLOAT_CLOSURE_SELECTED_MEMBERS,
        )
        self.assertIn("Cake.Double.posinf64", self.big_int_compatibility)
        self.assertIn("Cake.Word64.fromInt 2047", self.big_int_compatibility)
        self.assertEqual(
            set(self.big_int_record["module"]["selected_members"]),
            subject.BIG_INT_SELECTED_MEMBERS,
        )
        self.assertEqual(
            self.big_int_record["module"]["representation"],
            "type big_int = int",
        )
        self.assertEqual(
            set(self.big_int_record["num_bridge"]["overlay_members"]),
            subject.NUM_OVERLAY_MEMBERS,
        )
        self.assertEqual(
            set(self.big_int_record["num_toplevel"]["overlay_members"]),
            subject.NUM_TOPLEVEL_OVERLAY_MEMBERS,
        )
        self.assertEqual(
            set(self.big_int_record["num_bridge"][
                "closure_selected_members"
            ]),
            subject.NUM_CLOSURE_SELECTED_MEMBERS,
        )
        self.assertIn("failwith \"big_int_of_ratio\"", self.big_int_compatibility)
        self.assertIn(self.big_int_compatibility, self.driver)
        self.assertLess(
            self.driver.index(self.big_int_compatibility),
            self.driver.index('needs "arith_options.hl";;'),
        )

    def test_native_num_inventory_is_mechanically_closed(self) -> None:
        observed = set()
        for record in self.records:
            text = Path(record["physical_path"]).read_text(
                encoding="utf-8", errors="surrogateescape",
            )
            observed.update(
                match.group(1)
                for match in subject.NUM_NATIVE_MEMBER_RE.finditer(text)
            )
        self.assertEqual(observed, subject.NUM_CLOSURE_SELECTED_MEMBERS)

    def test_native_float_constant_inventory_is_mechanically_closed(self) -> None:
        observed = set()
        scanner = subject.flyspeck_nonlinear_verifier_closure.flyspeck_manifest
        for record in self.records:
            text = Path(record["physical_path"]).read_text(
                encoding="utf-8", errors="surrogateescape",
            )
            masked = scanner._code_mask(scanner.strip_ocaml_comments(text))
            observed.update(
                match.group(1)
                for match in subject.FLOAT_NATIVE_MEMBER_RE.finditer(masked)
            )
        self.assertEqual(observed, subject.FLOAT_CLOSURE_SELECTED_MEMBERS)

    def test_normalized_closure_has_no_active_general_formatting(self) -> None:
        for record in self.records:
            if record["normalization"] is None:
                continue
            text = record["normalized_bytes"].decode("latin-1")
            scanner = subject.flyspeck_nonlinear_verifier_closure.flyspeck_manifest
            masked = scanner._code_mask(scanner.strip_ocaml_comments(text))
            self.assertNotIn("sprintf", masked, record["source_key"])
            self.assertNotIn(
                "formatter_of_out_channel", masked, record["source_key"],
            )
            self.assertNotRegex(masked, r"(?<![A-Za-z0-9_'])assert\s*\(")

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
        self.assertNotIn("Printf.sprintf", self.driver)
        self.assertIn("string_of_float", self.driver)

    def test_gate_requires_exact_theorem_interface_and_axiom_stability(self) -> None:
        self.assertIn("hyp candle_nonlinear_smoke_theorem <> []", self.driver)
        self.assertIn(
            "concl candle_nonlinear_smoke_theorem <> "
            "candle_nonlinear_smoke_term",
            self.driver,
        )
        self.assertIn("candle_nonlinear_axioms_before", self.driver)
        self.assertIn("candle_nonlinear_axioms_after", self.driver)

    def test_closure_ready_marker_is_guarded_by_exported_value(self) -> None:
        identity = self.closure_driver.index(
            "nonlinear verifier loader identity did not commit"
        )
        exported = self.closure_driver.index(
            "M_verifier_main.verify_ineq", identity,
        )
        ready = self.closure_driver.index(subject.LOAD_MARKER, exported)
        self.assertLess(identity, exported)
        self.assertLess(exported, ready)
        self.assertIn(
            "else\n  let _ = M_verifier_main.verify_ineq",
            self.closure_driver,
        )
        self.assertNotIn(subject.PASS_MARKER, self.closure_driver)
        self.assertNotIn("candle_nonlinear_smoke_term", self.closure_driver)

    def test_absolute_driver_keeps_unprefixed_resolver_entry(self) -> None:
        stdin = subject.build_stdin(
            ROOT, Path("/tmp/support"), Path("/tmp/run/driver.ml"),
        )
        self.assertIn("Filename.currentDir", stdin)
        self.assertIn('#use "/tmp/run/driver.ml";;', stdin)


if __name__ == "__main__":
    unittest.main()
