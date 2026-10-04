#!/usr/bin/env python3
"""Materialize the direct-state ``mk_funs`` exception compatibility overlay.

Native HOL Light term destructors raise ``Failure`` when a binary-term probe
reaches a unary node.  In the current Candle direct state the corresponding
partial pattern raises ``Bind``.  Flyspeck's ``mk_funs`` deliberately uses
that failure to select its unary branch, so the direct source must catch both
representations of the same failed structural probe.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
SOURCE_KEY = "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
INPUT_SHA256 = "39d4f5b9c45b329e3f620e82eb5d3b44355a103ec9644828983e2b3e6cb9338b"
NORMALIZATION_ID = "candle-nonlinear-direct-mk-funs-bind-v1"
BEFORE = b"try mk_bin n pp x_var body_tm with Failure _ ->\n"
AFTER = b"try mk_bin n pp x_var body_tm with Failure _ | Bind ->\n"


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
        raise ValueError("direct mk_funs source is absent or duplicated")
    record = matches[0]
    source = record["normalized_bytes"]
    if (
        hashlib.sha256(source).hexdigest() != INPUT_SHA256
        or source.count(BEFORE) != 1
        or source.count(AFTER) != 0
    ):
        raise ValueError("direct mk_funs source or replacement anchor drift")

    normalized = source.replace(BEFORE, AFTER, 1)
    destination = output_root / "flyspeck" / record["logical_relative_path"]
    destination.parent.mkdir(parents=True)
    destination.write_bytes(normalized)
    payload = {
        "schema": 1,
        "kind": "candle-nonlinear-direct-mk-funs-overlay",
        "status": "development-non-release",
        "claim": (
            "one exact exception-representation compatibility adaptation; "
            "no theorem, hypothesis, proof, certificate, axiom, S2, S3, "
            "promotion, or release credit"
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
            "kind": "catch-candle-bind-as-failed-binary-term-probe",
            "replacement_count": 1,
            "before": BEFORE.decode("ascii"),
            "after": AFTER.decode("ascii"),
        },
    }
    receipt = output_root / "direct-mk-funs-overlay-receipt.json"
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
