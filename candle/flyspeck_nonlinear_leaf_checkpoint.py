#!/usr/bin/env python3
"""Prepare the clean predecessor checkpoint for first-leaf experiments.

The bundle authenticates and loads the complete nonlinear verifier closure and
the three native reconstruction modules, then stops before target
reconstruction, certificate search, Taylor construction, or formal proof.
Disposable checkpoint restores can therefore vary only the focused experiment
without replaying the analytic closure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_analytic_segmentation as analytic_segmentation
import flyspeck_nonlinear_first_leaf as first_leaf
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = 1


def prepare(
    flyspeck_root: Path,
    runtime: Path,
    generated_insulate: Path,
    output_root: Path,
) -> dict[str, Any]:
    """Materialize one source-authenticated first-leaf predecessor bundle."""

    candle_root = ROOT.resolve()
    flyspeck_root = flyspeck_root.resolve()
    runtime = runtime.resolve()
    generated_insulate = generated_insulate.resolve()
    output_root = output_root.resolve()
    if output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")
    smoke._ordinary_file(runtime, "Candle runtime")
    smoke._ordinary_file(
        generated_insulate, "Candle generated insulation support",
    )

    closure_data, closure, closure_records = smoke.authenticate_closure(
        candle_root, flyspeck_root,
    )
    segmentation = analytic_segmentation.segment_records(closure_records)
    target_data, target, support_records = first_leaf.authenticate_target(
        flyspeck_root, closure_data,
    )
    records = closure_records + support_records
    big_int_compatibility, big_int_record = (
        smoke.authenticate_big_int_compatibility(candle_root)
    )

    output_root.mkdir(parents=True)
    overlays = smoke.materialize_normalizations(output_root, records)
    support_root = output_root / "base-support"
    support_insulate = support_root / "candle/build/insulate.ml"
    support_insulate.parent.mkdir(parents=True)
    with support_insulate.open("xb") as destination:
        destination.write(generated_insulate.read_bytes())
    support_insulate.chmod(0o444)
    if smoke._hash_file(support_insulate, "sha256") != smoke._hash_file(
        generated_insulate, "sha256",
    ):
        raise ValueError("materialized generated insulation support drift")

    driver = output_root / "driver.ml"
    setup = output_root / "setup.ml"
    driver.write_text(
        smoke.build_driver(
            candle_root,
            flyspeck_root,
            records,
            overlays,
            big_int_compatibility,
            closure_only=True,
        )
        + first_leaf.build_target_prelude(
            target,
            flyspeck_root,
            support_records,
            first_leaf.SUPPORT_READY_MARKER,
        ),
        encoding="ascii",
        newline="\n",
    )
    setup.write_text(
        smoke.build_stdin(candle_root, support_root, driver),
        encoding="ascii",
        newline="\n",
    )

    payload = {
        "schema": RESULT_SCHEMA,
        "kind": "candle-flyspeck-nonlinear-first-leaf-checkpoint-input",
        "status": "development-non-release",
        "claim": (
            "authenticated nonlinear closure and first-leaf reconstruction "
            "support input; stops before reconstruction, search, Taylor "
            "construction, or proof; not a checkpoint, proof, cumulative, "
            "S2, S3, qualification, promotion, or release result"
        ),
        "ready_marker": first_leaf.SUPPORT_READY_MARKER,
        "candle_commit": smoke._git_head(candle_root),
        "closure": {
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"][
                "commit"
            ],
        },
        "target": {
            "bytes": len(target_data),
            "sha256": hashlib.sha256(target_data).hexdigest(),
            "id": target["target"]["id"],
            "global_case": target["target"]["global_case"],
            "local_case": target["target"]["local_case"],
            "legacy_oracle_digest": target["native_oracle"][
                "legacy_theorem_digest"
            ],
        },
        "closure_source_node_count": len(closure_records),
        "support_source_node_count": len(support_records),
        "source_node_count": len(records),
        "normalized_source_count": len(overlays),
        "segmentation": segmentation,
        "target_support": [
            {
                "source_key": record["source_key"],
                "physical_path": record["physical_path"],
                "bytes": int(record["bytes"]),
                "md5": record["md5"],
                "sha256": record["sha256"],
                "normalization": record["normalization"],
            }
            for record in support_records
        ],
        "big_int_compatibility": big_int_record,
        "runtime": smoke._record_file(runtime),
        "generated_insulation_input": smoke._record_file(
            generated_insulate
        ),
        "generated_insulation_support": smoke._record_file(
            support_insulate
        ),
        "controller": smoke._record_file(Path(__file__).resolve()),
        "driver": smoke._record_file(driver),
        "setup": smoke._record_file(setup),
    }
    receipt = output_root / "input-receipt.json"
    with receipt.open("x", encoding="utf-8") as destination:
        json.dump(payload, destination, indent=2, sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--generated-insulate", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    arguments = parser.parse_args()
    payload = prepare(
        arguments.flyspeck_root,
        arguments.runtime,
        arguments.generated_insulate,
        arguments.output_root,
    )
    print(json.dumps({
        "driver": payload["driver"],
        "ready_marker": payload["ready_marker"],
        "segmented_chunks": payload["segmentation"]["chunk_count"],
        "source_nodes": payload["source_node_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
