#!/usr/bin/env python3
"""Apply both exact large-module segmentations for analytic verification."""

from __future__ import annotations

from typing import Any

import flyspeck_nonlinear_module_segmentation as taylor
import flyspeck_nonlinear_multivariate_segmentation as multivariate


NORMALIZATION_ID = "candle-nonlinear-analytic-module-segmentation-v1"


def segment_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    sources = [
        taylor.segment_records(records),
        multivariate.segment_records(records),
    ]
    return {
        "normalization_id": NORMALIZATION_ID,
        "source_count": len(sources),
        "chunk_count": sum(source["chunk_count"] for source in sources),
        "marker_count": sum(source["marker_count"] for source in sources),
        "sources": sources,
    }
