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
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-minimal"
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
            self.assertEqual(
                hashlib.sha256((output / "driver.ml").read_bytes()).hexdigest(),
                receipt["driver"]["sha256"],
            )
            self.assertEqual(
                hashlib.sha256((output / "setup.ml").read_bytes()).hexdigest(),
                receipt["setup"]["sha256"],
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
