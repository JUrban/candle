#!/usr/bin/env python3

import hashlib
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
RUNTIME = Path(
    "/project/flyspeck-candle-runs/"
    "nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001/cake"
)
GENERATED_INSULATE = Path(
    "/project/worktrees/candle-action165-invf-v61/"
    "candle/build/insulate.ml"
)
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_first_leaf as first_leaf
import flyspeck_nonlinear_leaf_checkpoint as subject
import flyspeck_nonlinear_verifier_smoke as smoke


class NonlinearLeafCheckpointInputTest(unittest.TestCase):
    def test_prepares_clean_first_leaf_predecessor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "input"
            result = subject.prepare(
                FLYSPECK_ROOT, RUNTIME, GENERATED_INSULATE, output,
            )
            driver = (output / "driver.ml").read_text(encoding="ascii")
            suffix = (output / "post-analytic-suffix.ml").read_text(
                encoding="ascii",
            )
            setup = (output / "setup.ml").read_text(encoding="ascii")
            receipt_data = (output / "input-receipt.json").read_bytes()
            receipt = json.loads(receipt_data)

            self.assertEqual(result, receipt)
            self.assertEqual(result["closure_source_node_count"], 90)
            self.assertEqual(result["support_source_node_count"], 3)
            self.assertEqual(result["source_node_count"], 93)
            self.assertEqual(result["segmentation"]["chunk_count"], 17)
            self.assertEqual(result["ready_marker"], first_leaf.SUPPORT_READY_MARKER)
            self.assertIn(smoke.LOAD_MARKER, driver)
            self.assertIn(first_leaf.SUPPORT_READY_MARKER, driver)
            self.assertIn(
                'needs "azure/flyspeck-nat/break_case.hl"', driver,
            )
            self.assertNotIn("Break_case.ineqm_conv", driver)
            self.assertNotIn("candle_nonlinear_first_leaf_eq", driver)
            self.assertLess(
                driver.index(smoke.LOAD_MARKER),
                driver.index(first_leaf.SUPPORT_READY_MARKER),
            )
            self.assertIn("#use", setup)
            self.assertIn(str(ROOT.resolve()), setup)
            self.assertNotIn('#use "hol.ml"', suffix)
            self.assertIn("let candle_binary64_abs", suffix)
            self.assertIn("Cake.Double.significand x", suffix)
            self.assertIn("let candle_array_to_list", suffix)
            self.assertIn("Cake.Array.sub a index", suffix)
            self.assertIn("let candle_ignore _ = ()", suffix)
            self.assertIn(
                "post-analytic checkpoint source identity mismatch", suffix,
            )
            self.assertIn(
                "post-analytic verifier loader identity did not commit", suffix,
            )
            self.assertIn(
                subject.POST_ANALYTIC_CLOSURE_READY_REF, suffix,
            )
            self.assertNotIn("Cakeml.configureSourceIdentities", suffix)
            self.assertNotIn("Cakeml.configureNormalizationOverlay", suffix)
            self.assertIn(
                "post-analytic inherited source identity table mismatch",
                suffix,
            )
            self.assertIn(
                "List.iter candle_nonlinear_check_overlay "
                "candle_nonlinear_overlay_rows",
                suffix,
            )
            self.assertIn(
                "Cakeml.normalizationOverlay :=", suffix,
            )
            self.assertIn(
                "post-analytic inherited loader overlay mismatch", suffix,
            )
            self.assertIn(
                "post-analytic overlay delta contract mismatch", suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/verifier/"
                    "m_verifier.hl"
                ),
                suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/trig/"
                    "exp_eval.hl"
                ),
                suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/informal/"
                    "informal_exp.hl"
                ),
                suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/informal/"
                    "informal_nat.hl"
                ),
                suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/informal/"
                    "informal_search.hl"
                ),
                suffix,
            )
            self.assertIn(
                str(
                    output / "overlay/flyspeck/formal_ineqs/informal/"
                    "informal_verifier.hl"
                ),
                suffix,
            )
            self.assertNotIn(
                "post-analytic direct source was already loaded:", suffix,
            )
            self.assertNotIn(
                "post-analytic direct source dependency did not commit:",
                suffix,
            )
            self.assertEqual(
                suffix.count("post-analytic overlay delta contract mismatch"),
                1,
            )
            self.assertEqual(
                len(subject.POST_ANALYTIC_OVERLAY_DELTA_SPECS), 10,
            )
            self.assertIn(first_leaf.SUPPORT_READY_MARKER, suffix)
            self.assertNotIn("Break_case.ineqm_conv", suffix)
            self.assertEqual(suffix.count("M_verifier_main.verify_ineq"), 1)
            self.assertLess(
                suffix.index(smoke.LOAD_MARKER),
                suffix.index(first_leaf.SUPPORT_READY_MARKER),
            )
            self.assertEqual(
                hashlib.sha256((output / "driver.ml").read_bytes()).hexdigest(),
                receipt["driver"]["sha256"],
            )
            self.assertEqual(
                hashlib.sha256((output / "setup.ml").read_bytes()).hexdigest(),
                receipt["setup"]["sha256"],
            )
            self.assertEqual(
                hashlib.sha256(
                    (output / "post-analytic-suffix.ml").read_bytes()
                ).hexdigest(),
                receipt["post_analytic_suffix"]["sha256"],
            )
            self.assertEqual(
                set(receipt[
                    "post_analytic_binary64_abs_compatibility"
                ]["overlay_members"]),
                smoke.BINARY64_ABS_MEMBERS,
            )
            self.assertEqual(
                set(receipt[
                    "post_analytic_array_to_list_compatibility"
                ]["overlay_members"]),
                smoke.ARRAY_TO_LIST_MEMBERS,
            )
            self.assertEqual(
                set(receipt[
                    "post_analytic_ignore_compatibility"
                ]["overlay_members"]),
                smoke.IGNORE_MEMBERS,
            )

    def test_refuses_to_overwrite_an_existing_output_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(ValueError, "already exists"):
                subject.prepare(
                    FLYSPECK_ROOT,
                    RUNTIME,
                    GENERATED_INSULATE,
                    Path(temporary),
                )


if __name__ == "__main__":
    unittest.main()
