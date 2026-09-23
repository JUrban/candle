#!/usr/bin/env python3

import copy
import hashlib
import unittest
from pathlib import Path

import flyspeck_nonlinear_multivariate_segmentation as segmentation
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
FLYSPECK = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)


class NonlinearMultivariateSegmentationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        _,_,cls.records = smoke.authenticate_closure(ROOT,FLYSPECK)

    def test_exact_segmentation_and_public_interface(self) -> None:
        records = copy.deepcopy(self.records)
        original_record = next(
            item for item in records if item["source_key"] == segmentation.SOURCE_KEY
        )
        original = original_record["normalized_bytes"]
        body = original.split(segmentation.MODULE_ANCHOR,1)[1].split(
            segmentation.CLOSE_ANCHOR,1
        )[0]
        expected_chunks = segmentation._split_body(body)
        receipt = segmentation.segment_records(records)
        record = next(
            item for item in records if item["source_key"] == segmentation.SOURCE_KEY
        )
        data = record["normalized_bytes"]
        text = data.decode("ascii")

        self.assertEqual(receipt["chunk_count"],10)
        self.assertEqual(receipt["marker_count"],20)
        self.assertEqual(b"".join(expected_chunks),body)
        self.assertEqual(
            [entry["bytes"] for entry in receipt["chunks"]],
            [len(chunk) for chunk in expected_chunks],
        )
        self.assertEqual(
            receipt["normalized_sha256"],hashlib.sha256(data).hexdigest()
        )
        self.assertEqual(
            record["normalization"]["id"],segmentation.NORMALIZATION_ID
        )
        self.assertEqual(text.count(segmentation.MARKER_PREFIX),20)
        self.assertEqual(text.count("module Candle_multivariate_taylor_chunk_"),10)
        self.assertEqual(
            text.count("include Candle_multivariate_taylor_chunk_"),10
        )
        self.assertIn("module Multivariate_taylor = struct\n",text)
        self.assertTrue(text.endswith(
            "include Candle_multivariate_taylor_chunk_009;;\nend;;\n"
        ))

    def test_later_chunks_restore_original_open_precedence(self) -> None:
        records = copy.deepcopy(self.records)
        segmentation.segment_records(records)
        record = next(
            item for item in records if item["source_key"] == segmentation.SOURCE_KEY
        )
        data = record["normalized_bytes"]
        for index in range(1,10):
            previous = segmentation._module_name(index - 1).encode("ascii")
            anchor = segmentation.DEPENDENCY_OPENS + b"include " + previous + b";;\n"
            self.assertEqual(data.count(anchor),1)

    def test_identity_and_anchor_drift_fail_closed(self) -> None:
        records = copy.deepcopy(self.records)
        record = next(
            item for item in records if item["source_key"] == segmentation.SOURCE_KEY
        )
        record["normalized_bytes"] += b"\n"
        with self.assertRaisesRegex(ValueError,"identity drift"):
            segmentation.segment_records(records)
        body = b"prefix" + segmentation.SPLIT_ANCHORS[0] + b"suffix"
        with self.assertRaisesRegex(ValueError,"absent or duplicated"):
            segmentation._split_body(body)


if __name__ == "__main__":
    unittest.main()
