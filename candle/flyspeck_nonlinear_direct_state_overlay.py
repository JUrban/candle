#!/usr/bin/env python3
"""Materialize the one context-specific direct-state verifier adaptation.

The authenticated direct Flyspeck prefix has already defined ``list_sum`` in
``Seq2``.  The standalone Formal_ineqs verifier source normally defines the
same named constant before proving its ITLIST recursion contract.  In the
combined direct state, the second ``new_definition`` must fail closed.  This
overlay replaces only that ML binding with the independently proved theorem
``candle_cv_direct_list_sum_as_itlist``; the logical constant, theorem
statement, and all remaining source bytes are retained.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
SOURCE_KEY = "flyspeck:formal_ineqs/list/list_float.hl"
INPUT_SHA256 = "4b095f53e5137fb81f67cd4529e65aa51d8fb6951b7b7067113338abcef844ad"
NORMALIZATION_ID = "candle-nonlinear-direct-list-sum-reuse-v1"
COMPATIBILITY_SOURCE = Path(
    "candle/cv_compute_nonlinear_direct_list_sum_compat.ml"
)
BEFORE = (
    b"let list_sum = new_definition `list_sum list f = ITLIST "
    b"(\\t1 t2. f t1 + t2) list (&0)`;;\r\n"
)
AFTER = b"let list_sum = candle_cv_direct_list_sum_as_itlist;;\r\n"


def _identity(data: bytes) -> dict[str, Any]:
    return {
        "bytes": len(data),
        "md5": hashlib.md5(data, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def run(flyspeck_root: Path, output_root: Path) -> dict[str, Any]:
    flyspeck_root = flyspeck_root.resolve()
    output_root = output_root.resolve()
    if output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")

    closure_data, closure, records = smoke.authenticate_closure(
        ROOT, flyspeck_root,
    )
    matches = [record for record in records if record["source_key"] == SOURCE_KEY]
    if len(matches) != 1:
        raise ValueError("direct list-sum source is absent or duplicated")
    record = matches[0]
    source = record["normalized_bytes"]
    if (
        hashlib.sha256(source).hexdigest() != INPUT_SHA256
        or record.get("normalization") is not None
        or source.count(BEFORE) != 1
        or source.count(AFTER) != 0
    ):
        raise ValueError("direct list-sum source or replacement anchor drift")

    normalized = source.replace(BEFORE, AFTER, 1)
    compatibility_path = ROOT / COMPATIBILITY_SOURCE
    compatibility = compatibility_path.read_bytes()
    if compatibility.count(b"let candle_cv_direct_list_sum_as_itlist = prove") != 1:
        raise ValueError("direct list-sum compatibility theorem drift")

    destination = output_root / "flyspeck" / record["logical_relative_path"]
    destination.parent.mkdir(parents=True)
    destination.write_bytes(normalized)
    payload = {
        "schema": 1,
        "kind": "candle-nonlinear-direct-state-overlay",
        "status": "development-non-release",
        "claim": (
            "one exact ML theorem-binding reuse after an authenticated direct "
            "source prefix; no new logical constant, axiom, proof shortcut, "
            "S2, S3, promotion, or release credit"
        ),
        "normalization_id": NORMALIZATION_ID,
        "closure": {
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"]["commit"],
        },
        "source_key": SOURCE_KEY,
        "logical_relative_path": record["logical_relative_path"],
        "input": _identity(source),
        "output": _identity(normalized),
        "operation": {
            "kind": "reuse-proved-existing-logical-constant-contract",
            "replacement_count": 1,
            "before": BEFORE.decode("ascii"),
            "after": AFTER.decode("ascii"),
        },
        "compatibility_theorem_source": {
            "path": COMPATIBILITY_SOURCE.as_posix(),
            **_identity(compatibility),
        },
    }
    receipt = output_root / "direct-state-overlay-receipt.json"
    with receipt.open("x", encoding="utf-8") as destination_file:
        json.dump(payload, destination_file, indent=2, sort_keys=True)
        destination_file.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    arguments = parser.parse_args()
    payload = run(arguments.flyspeck_root, arguments.output_root)
    print(json.dumps({
        "normalization_id": payload["normalization_id"],
        "output_root": str(arguments.output_root.resolve()),
        "output_sha256": payload["output"]["sha256"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
