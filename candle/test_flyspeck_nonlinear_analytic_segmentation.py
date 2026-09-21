#!/usr/bin/env python3

import copy
import unittest
from pathlib import Path

import flyspeck_nonlinear_analytic_segmentation as segmentation
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
FLYSPECK = Path("/project/worktrees/flyspeck-v13-source")


class NonlinearAnalyticSegmentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        _,_,cls.records = smoke.authenticate_closure(ROOT,FLYSPECK)

    def test_both_exact_sources_are_segmented(self) -> None:
        records = copy.deepcopy(self.records)
        receipt = segmentation.segment_records(records)
        self.assertEqual(receipt["source_count"],2)
        self.assertEqual(receipt["chunk_count"],17)
        self.assertEqual(receipt["marker_count"],34)
        self.assertEqual(
            {source["public_module"] for source in receipt["sources"]},
            {"Taylor_interval","Multivariate_taylor"},
        )
        normalized = {
            record["source_key"]: record["normalization"]["id"]
            for record in records
            if record["normalization"] is not None
        }
        for source in receipt["sources"]:
            self.assertEqual(
                normalized[source["source_key"]],source["normalization_id"]
            )


if __name__ == "__main__":
    unittest.main()
