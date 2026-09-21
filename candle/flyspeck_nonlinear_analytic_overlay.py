#!/usr/bin/env python3
"""Materialize the exact dual-segmented analytic closure overlay."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import flyspeck_nonlinear_analytic_segmentation as segmentation
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]


def run(flyspeck_root: Path,output_root: Path) -> dict:
    flyspeck_root = flyspeck_root.resolve()
    output_root = output_root.resolve()
    if output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")
    closure_data,closure,records = smoke.authenticate_closure(ROOT,flyspeck_root)
    receipt = segmentation.segment_records(records)
    output_root.mkdir(parents=True)
    overlays = smoke.materialize_normalizations(output_root,records)
    payload = {
        "schema": 1,
        "kind": "candle-nonlinear-analytic-segmented-overlay",
        "status": "development-non-release",
        "claim": (
            "exact authenticated source normalization only; no parsing, "
            "execution, proof, S2, S3, promotion, or release credit"
        ),
        "closure": {
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"]["commit"],
        },
        "segmentation": receipt,
        "normalized_source_count": len(overlays),
        "normalized_sources": overlays,
    }
    result = output_root / "overlay-receipt.json"
    with result.open("x",encoding="utf-8") as destination:
        json.dump(payload,destination,indent=2,sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root",type=Path,required=True)
    parser.add_argument("--output-root",type=Path,required=True)
    arguments = parser.parse_args()
    payload = run(arguments.flyspeck_root,arguments.output_root)
    print(json.dumps({
        "normalization": payload["segmentation"]["normalization_id"],
        "normalized_source_count": payload["normalized_source_count"],
        "output_root": str(arguments.output_root.resolve()),
    },sort_keys=True))


if __name__ == "__main__":
    main()
