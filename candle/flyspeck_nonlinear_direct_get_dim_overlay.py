#!/usr/bin/env python3
"""Materialize the direct-state ``M_taylor.get_dim`` compatibility overlay.

The native source expresses the decoder as a long composition of ordinary
type destructors.  In the loaded direct Flyspeck namespace that unqualified
composition raises ``Bind`` even for ``cart(real,6)``.  The replacement makes
the same applications and selection order explicit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
SOURCE_KEY = "flyspeck:formal_ineqs/taylor/m_taylor.hl"
INPUT_SHA256 = "bfc3f686c2b76d4d5fac7c05fb7d84d9dbc736f3f1fa3ceb486a042969b55116"
NORMALIZATION_ID = "candle-nonlinear-direct-get-dim-explicit-v7"
BEFORE = (
    b"let get_dim = int_of_string o fst o dest_type o hd o tl o snd o "
    b"dest_type o type_of;;\r\n"
)
AFTER = (
    b"let get_dim tm =\r\n"
    b"  let _,type_arguments =\r\n"
    b"    Kernel.dest_type (Kernel.call_type_of tm) in\r\n"
    b"  let dimension_type =\r\n"
    b"    match type_arguments with\r\n"
    b"    | _ :: dimension :: _ -> dimension\r\n"
    b"    | _ -> failwith \"get_dim\" in\r\n"
    b"  let rec find_dimension index =\r\n"
    b"    if index > max_dim then failwith \"get_dim\"\r\n"
    b"    else if dimension_type = n_type_array.(index) then index\r\n"
    b"    else find_dimension (index + 1) in\r\n"
    b"  find_dimension 1;;\r\n"
)
INLINE_BEFORE = (
    b"(int_of_string o fst o dest_type o hd o tl o snd o dest_type o "
    b"type_of) x_var"
)
INLINE_AFTER = b"get_dim x_var"
INLINE_AFTER_BASE_COUNT = 6


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
        raise ValueError("direct get_dim source is absent or duplicated")
    record = matches[0]
    source = record["normalized_bytes"]
    if (
        hashlib.sha256(source).hexdigest() != INPUT_SHA256
        or source.count(BEFORE) != 1
        or source.count(AFTER) != 0
        or source.count(INLINE_BEFORE) != 2
        or source.count(INLINE_AFTER) != INLINE_AFTER_BASE_COUNT
    ):
        raise ValueError("direct get_dim source or replacement anchor drift")

    normalized = source.replace(BEFORE, AFTER, 1)
    normalized = normalized.replace(INLINE_BEFORE, INLINE_AFTER)
    destination = output_root / "flyspeck" / record["logical_relative_path"]
    destination.parent.mkdir(parents=True)
    destination.write_bytes(normalized)
    payload = {
        "schema": 1,
        "kind": "candle-nonlinear-direct-get-dim-overlay",
        "status": "development-non-release",
        "claim": (
            "one exact direct-name-resolution normalization identifying the "
            "selected dimension type against the module's authoritative "
            "bounded dimension-type array and reusing that decoder at both "
            "internal call sites; no theorem, proof, "
            "certificate, axiom, S2, S3, promotion, or release credit"
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
            "kind": "bounded-dimension-type-array-lookup",
            "replacement_count": 1,
            "inline_reuse_count": 2,
            "before": BEFORE.decode("ascii"),
            "after": AFTER.decode("ascii"),
            "inline_before": INLINE_BEFORE.decode("ascii"),
            "inline_after": INLINE_AFTER.decode("ascii"),
        },
    }
    receipt = output_root / "direct-get-dim-overlay-receipt.json"
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
