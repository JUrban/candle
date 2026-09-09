#!/usr/bin/env python3
"""Non-authorizing direct-loader relocation check against an actual plan.

This copies the plan's authenticated source and normalization bytes below a
fresh temporary root, rebuilds the loader-owned source-trace contract in both
locations, and requires identical logical binding identities.  It does not run
Candle and cannot produce S2/S3 or release evidence.
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
PROGRAM_PATH = Path(__file__).resolve()
sys.path.insert(0, str(HERE))
import flyspeck_stratum_runtime as runtime


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def load(path: Path, label: str) -> dict[str, Any]:
    value = runtime.load_object(path, label)
    runtime.require(isinstance(value, dict), f"malformed {label}")
    return value


def copy_exact(source: Path, root: Path, relative: str,
               expected: dict[str, Any]) -> Path:
    target_relative = runtime.safe_relative(relative, "relocation dry-run")
    target = root / target_relative
    runtime.require(source.is_file() and not source.is_symlink(),
                    f"non-ordinary relocation source: {source}")
    runtime.validate_file(source, expected, "relocation dry-run source")
    target.parent.mkdir(parents=True, exist_ok=True)
    runtime.require(not target.exists() and not target.is_symlink(),
                    f"relocation destination collision: {target}")
    shutil.copyfile(source, target)
    runtime.validate_file(target, expected, "relocated dry-run source")
    runtime.require(target.stat().st_nlink == 1,
                    f"relocated source is hard-linked: {target}")
    return target


def source_records(plan: dict[str, Any]) -> list[dict[str, Any]]:
    graph = plan.get("source_graph")
    runtime.require(isinstance(graph, dict), "missing plan source graph")
    records = graph.get("bindings")
    runtime.require(isinstance(records, list) and
                    graph.get("entry_count") == len(records) == 400 and
                    graph.get("ordered_binding_sha256") ==
                    runtime.canonical_sha256(records),
                    "malformed plan source graph")
    return records


def normalization_records(plan: dict[str, Any]) -> list[dict[str, Any]]:
    overlay = plan.get("normalization_overlay")
    runtime.require(isinstance(overlay, dict), "missing normalization overlay")
    records = overlay.get("bindings")
    runtime.require(isinstance(records, list) and
                    overlay.get("entry_count") == len(records) and
                    overlay.get("ordered_binding_sha256") ==
                    runtime.canonical_sha256(records),
                    "malformed normalization overlay")
    return records


def build_prepared(
    manifest: dict[str, Any], sources: list[dict[str, Any]],
    normalizations: list[dict[str, Any]], candle_root: Path,
    flyspeck_root: Path, overlay_root: Path,
) -> dict[str, Any]:
    source_by_key = {record["key"]: record for record in sources}
    runtime.require(len(source_by_key) == len(sources),
                    "duplicate source key in relocation dry run")
    source_runtime = []
    for record in sources:
        root = candle_root if record["repository"] == "candle" else flyspeck_root
        path = root / runtime.safe_relative(record["path"], "source binding")
        runtime.validate_file(path, record, f"source binding {record['key']}")
        source_runtime.append({**record, "absolute": str(path)})

    digest_path = candle_root / runtime.SOURCE_DIGEST_RELATIVE
    digest = runtime.hash_file(digest_path)
    loader_artifacts = {
        **source_by_key,
        "candle:candle/flyspeck_source_digests.ml": {
            "key": "candle:candle/flyspeck_source_digests.ml",
            "repository": "candle",
            "path": runtime.SOURCE_DIGEST_RELATIVE.as_posix(),
            "artifact_role": "generated-runtime-control",
            **digest,
        },
    }
    source_alias_runtime = runtime.validate_source_alias_contract(
        manifest, source_by_key, candle_root, flyspeck_root,
    )
    source_loader_runtime = runtime.derive_source_loader_runtime(
        manifest, loader_artifacts, candle_root, flyspeck_root,
    )
    normalized_runtime = []
    for record in normalizations:
        source = source_by_key[record["source_key"]]
        source_root = (
            candle_root if source["repository"] == "candle" else flyspeck_root
        )
        original = source_root / source["path"]
        output = overlay_root / record["path"]
        expected = {
            "bytes": record["normalized_bytes"],
            "sha256": record["normalized_sha256"],
            "md5": record["normalized_md5"],
        }
        runtime.validate_file(output, expected,
                              f"normalization {record['source_key']}")
        normalized_runtime.append({
            "source_key": record["source_key"],
            "normalization_id": record["id"],
            "relative": record["path"],
            "original_relative": source["path"],
            "original": str(original),
            "output": str(output),
            **expected,
        })
    return {
        "candle_runtime_root": candle_root,
        "flyspeck_root": flyspeck_root,
        "source_runtime": source_runtime,
        "source_alias_runtime": source_alias_runtime,
        "source_loader_runtime": source_loader_runtime,
        "normalized_runtime": normalized_runtime,
    }


def logical_projection(contract: dict[str, Any]) -> list[dict[str, Any]]:
    return sorted(
        ({
            "binding_id": binding["binding_id"],
            "logical_identity": binding["logical_identity"],
        } for binding in contract["bindings"]),
        key=lambda value: value["binding_id"],
    )


def run(plan_root: Path, attempt_root: Path) -> dict[str, Any]:
    plan_path = plan_root / "plan.json"
    materialization_path = plan_root / "host-materialization.json"
    attempt_path = attempt_root / "attempt.json"
    receipt_path = attempt_root / "receipt.json"
    plan = load(plan_path, "direct plan")
    materialization = load(materialization_path, "host materialization")
    attempt = load(attempt_path, "direct attempt")
    receipt = load(receipt_path, "direct receipt")
    runtime.require(receipt.get("boundary_id") == attempt.get("boundary_id") and
                    receipt.get("attempt_nonce") == attempt.get("attempt_nonce"),
                    "actual direct attempt and receipt identity mismatch")
    roots = materialization.get("host_roots")
    runtime.require(isinstance(roots, dict), "missing host materialization roots")
    candle_root = Path(roots["candle"])
    flyspeck_root = Path(roots["flyspeck"])
    overlay_root = Path(roots["normalization_overlay"])
    manifest_path = candle_root / runtime.MANIFEST_RELATIVE
    manifest = load(manifest_path, "Flyspeck manifest")
    sources = source_records(plan)
    normalizations = normalization_records(plan)
    closure = attempt.get("expected_logical_source_closure")
    runtime.require(isinstance(closure, dict),
                    "missing actual attempt logical source closure")
    nonce = attempt.get("attempt_nonce")
    runtime.require(isinstance(nonce, str), "missing actual attempt nonce")
    original_program = attempt_root / "control/instrumented-prefix.ml"
    original_postlude = attempt_root / "control/postlude.ml"

    original = build_prepared(
        manifest, sources, normalizations, candle_root, flyspeck_root,
        overlay_root,
    )
    original_contract = runtime.build_source_trace_contract(
        original, closure, original_program, original_postlude, [], nonce,
    )

    with tempfile.TemporaryDirectory(prefix="candle-loader-relocation-") as temporary:
        relocated = Path(temporary) / "authenticated-snapshot-relocation"
        relocated_candle = relocated / "candle"
        relocated_flyspeck = relocated / "flyspeck"
        relocated_overlay = relocated / "overlay"
        relocated_control = relocated / "control"
        for record in sources:
            old_root = candle_root if record["repository"] == "candle" else flyspeck_root
            new_root = (
                relocated_candle if record["repository"] == "candle"
                else relocated_flyspeck
            )
            copy_exact(old_root / record["path"], new_root,
                       record["path"], record)
        harness_paths = (
            runtime.SETUP_RELATIVE, runtime.SOURCE_DIGEST_RELATIVE,
            runtime.CHECK_RELATIVE, Path("candle/build/insulate.ml"),
        )
        for relative in harness_paths:
            source = candle_root / relative
            copy_exact(source, relocated_candle, relative.as_posix(),
                       runtime.hash_file(source))
        for record in normalizations:
            expected = {
                "bytes": record["normalized_bytes"],
                "sha256": record["normalized_sha256"],
                "md5": record["normalized_md5"],
            }
            copy_exact(overlay_root / record["path"], relocated_overlay,
                       record["path"], expected)
        relocated_program = copy_exact(
            original_program, relocated_control, "instrumented-prefix.ml",
            runtime.hash_file(original_program),
        )
        relocated_postlude = copy_exact(
            original_postlude, relocated_control, "postlude.ml",
            runtime.hash_file(original_postlude),
        )
        relocated_prepared = build_prepared(
            manifest, sources, normalizations, relocated_candle,
            relocated_flyspeck, relocated_overlay,
        )
        relocated_contract = runtime.build_source_trace_contract(
            relocated_prepared, closure, relocated_program,
            relocated_postlude, [], nonce,
        )
        original_logical = logical_projection(original_contract)
        relocated_logical = logical_projection(relocated_contract)
        runtime.require(original_logical == relocated_logical,
                        "logical loader authority changed after relocation")
        runtime.require(original_contract["ordered_binding_sha256"] !=
                        relocated_contract["ordered_binding_sha256"],
                        "relocation did not change run-local path observations")
        hol_bindings = [
            binding for binding in relocated_contract["bindings"]
            if binding["key"] == "candle:hol.ml"
        ]
        runtime.require(len(hol_bindings) == 1 and
                        hol_bindings[0]["resolved"] == "hol.ml" and
                        hol_bindings[0]["logical_identity"]["source_repository"] ==
                        "candle" and
                        hol_bindings[0]["logical_identity"]["source_relative_path"] ==
                        "hol.ml",
                        "initial lexical request did not bind exact manifest node")

    return {
        "schema": 1,
        "kind": "candle-direct-loader-real-plan-relocation-dry-run",
        "claim": (
            "Development validation only; no Candle execution, S2/S3 evidence, "
            "approval, or release claim."
        ),
        "completed_utc": utc_now(),
        "state": "passed",
        "promotion_allowed": False,
        "inputs": {
            "plan": {"path": str(plan_path), **runtime.hash_file(plan_path)},
            "host_materialization": {
                "path": str(materialization_path),
                **runtime.hash_file(materialization_path),
            },
            "attempt": {"path": str(attempt_path), **runtime.hash_file(attempt_path)},
            "receipt": {"path": str(receipt_path), **runtime.hash_file(receipt_path)},
            "manifest": {"path": str(manifest_path), **runtime.hash_file(manifest_path)},
        },
        "tools": {
            "dry_run": {
                "path": PROGRAM_PATH.name, **runtime.hash_file(PROGRAM_PATH),
            },
            "direct_runner": {
                "path": "flyspeck_stratum_runtime.py",
                **runtime.hash_file(HERE / "flyspeck_stratum_runtime.py"),
            },
        },
        "boundary_id": attempt.get("boundary_id"),
        "source_record_count": len(sources),
        "loader_resolution_count": len(original["source_loader_runtime"]),
        "logical_binding_count": len(original_logical),
        "original_observation_sha256": original_contract["ordered_binding_sha256"],
        "relocated_observation_sha256": relocated_contract["ordered_binding_sha256"],
        "logical_projection_sha256": runtime.canonical_sha256(original_logical),
        "logical_authority_unchanged": True,
        "absolute_observations_changed": True,
        "initial_request": "hol.ml",
        "initial_source_key": "candle:hol.ml",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("plan_root", type=Path)
    parser.add_argument("attempt_root", type=Path)
    parser.add_argument("--write-report", required=True, type=Path)
    arguments = parser.parse_args()
    runtime.require(not arguments.write_report.exists() and
                    not arguments.write_report.is_symlink(),
                    "dry-run report destination already exists")
    report = run(arguments.plan_root, arguments.attempt_root)
    arguments.write_report.parent.mkdir(parents=True, exist_ok=True)
    arguments.write_report.write_bytes(runtime.canonical_bytes(report) + b"\n")
    arguments.write_report.chmod(0o444)
    print(json.dumps(report, sort_keys=True, separators=(",", ":")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
