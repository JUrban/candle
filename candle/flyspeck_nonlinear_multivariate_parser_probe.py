#!/usr/bin/env python3
"""Parse the exact segmented multivariate Taylor source in one fresh process."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

import flyspeck_loader_quotation
import flyspeck_nonlinear_multivariate_segmentation as segmentation
import flyspeck_nonlinear_verifier_smoke as smoke
import flyspeck_parser_diagnostic as parser_diagnostic


ROOT = Path(__file__).resolve().parents[1]


def run(flyspeck_root: Path, runtime: Path, output: Path, timeout: int) -> dict:
    flyspeck_root = flyspeck_root.resolve()
    runtime = runtime.resolve()
    output = output.resolve()
    if output.exists():
        raise ValueError(f"result path already exists: {output}")
    _,_,records = smoke.authenticate_closure(ROOT,flyspeck_root)
    receipt = segmentation.segment_records(records)
    record = next(
        item for item in records if item["source_key"] == segmentation.SOURCE_KEY
    )
    closure = json.loads((ROOT / smoke.CLOSURE).read_bytes())
    node = closure["source_nodes"][segmentation.SOURCE_KEY]
    prepared,actions,unsupported,quotation = parser_diagnostic.prepare_source(
        segmentation.SOURCE_KEY,
        record["normalized_bytes"],
        node["dependencies"],
        flyspeck_loader_quotation,
    )
    if prepared is None or unsupported or quotation is None:
        raise ValueError(f"segmented parser preparation failed: {unsupported}")
    nonce = os.urandom(32).hex()
    started = time.monotonic()
    result = subprocess.run(
        [str(runtime),parser_diagnostic.RUN_ARGUMENT,nonce],
        input=prepared,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=runtime.parent,
        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
        timeout=timeout,
        check=False,
    )
    elapsed = time.monotonic() - started
    protocol = parser_diagnostic.parse_protocol_result(nonce,result)
    payload = {
        "schema": 1,
        "kind": "candle-nonlinear-multivariate-segmented-parser-probe",
        "status": "development-non-release",
        "outcome": protocol["outcome"],
        "elapsed_seconds": elapsed,
        "exit_code": result.returncode,
        "source_key": segmentation.SOURCE_KEY,
        "source_sha256": segmentation.INPUT_SHA256,
        "segmentation": receipt,
        "prepared_bytes": len(prepared),
        "prepared_sha256": hashlib.sha256(prepared).hexdigest(),
        "manifest_action_count": len(actions),
        "quotation_expansion": quotation,
        "stdout_bytes": len(result.stdout),
        "stdout_sha256": hashlib.sha256(result.stdout).hexdigest(),
        "stderr_bytes": len(result.stderr),
        "stderr_sha256": hashlib.sha256(result.stderr).hexdigest(),
        "parser_error": protocol["controller_stderr_digest"],
        "runtime": {
            "path": str(runtime),
            "bytes": runtime.stat().st_size,
            "sha256": smoke._hash_file(runtime,"sha256"),
        },
    }
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("x",encoding="utf-8") as destination:
        json.dump(payload,destination,indent=2,sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root",type=Path,required=True)
    parser.add_argument("--runtime",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    parser.add_argument("--timeout-seconds",type=int,default=3600)
    arguments = parser.parse_args()
    payload = run(
        arguments.flyspeck_root,arguments.runtime,arguments.output,
        arguments.timeout_seconds,
    )
    print(json.dumps({
        "outcome": payload["outcome"],
        "elapsed_seconds": payload["elapsed_seconds"],
        "result": str(arguments.output.resolve()),
    },sort_keys=True))
    if payload["outcome"] != "parse-ok":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
