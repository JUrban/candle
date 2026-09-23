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
RUNTIME = Path(
    "/project/flyspeck-candle-runs/"
    "nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001/cake"
)
GENERATED_INSULATE = Path(
    "/project/worktrees/candle-action165-invf-v61/"
    "candle/build/insulate.ml"
)
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_closure_checkpoint as subject
import flyspeck_nonlinear_verifier_smoke as smoke


class NonlinearClosureCheckpointInputTest(unittest.TestCase):
    def test_prepares_guarded_dual_segmented_closure_only_input(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "input"
            result = subject.prepare(
                FLYSPECK_ROOT, RUNTIME, GENERATED_INSULATE, output,
            )
            driver = (output / "driver.ml").read_text(encoding="ascii")
            setup = (output / "setup.ml").read_text(encoding="ascii")
            receipt = json.loads(
                (output / "input-receipt.json").read_text(encoding="utf-8")
            )

            self.assertEqual(result, receipt)
            self.assertEqual(result["source_node_count"], 90)
            self.assertEqual(result["segmentation"]["source_count"], 2)
            self.assertEqual(result["segmentation"]["chunk_count"], 17)
            self.assertEqual(
                [source["chunk_count"]
                 for source in result["segmentation"]["sources"]],
                [7, 10],
            )
            self.assertIn("M_verifier_main.verify_ineq", driver)
            self.assertIn(smoke.LOAD_MARKER, driver)
            self.assertNotIn(smoke.PASS_MARKER, driver)
            self.assertIn("#use", setup)
            self.assertIn(str(ROOT.resolve()), setup)

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
