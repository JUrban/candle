#!/usr/bin/env python3
"""Run a focused parser-only gate over the nonlinear verifier extension.

This is DEVELOPMENT / NON-RELEASE evidence.  It reuses the established
quotation preparation, manifest-action masking, parser capability handshake,
and response validator.  Each exact extension source is submitted to a fresh
parser-only process; no source is inferred or evaluated.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path
from typing import Any

import flyspeck_loader_quotation
import flyspeck_parser_diagnostic


ROOT = Path(__file__).resolve().parents[1]
CLOSURE = Path("candle/flyspeck_nonlinear_verifier_closure.json")
RESULT_SCHEMA = 1


def _hash_file(path: Path, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def _record_bytes(data: bytes) -> dict[str, Any]:
    return {
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _run_parser(
    runtime: Path,
    runtime_cwd: Path,
    arguments: list[str],
    source: bytes,
    timeout_seconds: int,
) -> tuple[subprocess.CompletedProcess[bytes], float]:
    started = time.monotonic()
    result = subprocess.run(
        [str(runtime), *arguments],
        input=source,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=runtime_cwd,
        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
        timeout=timeout_seconds,
        check=False,
    )
    return result, time.monotonic() - started


def run(
    flyspeck_root: Path,
    runtime: Path,
    output: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    flyspeck_root = flyspeck_root.resolve()
    runtime = runtime.resolve()
    output = output.resolve()
    if output.exists():
        raise ValueError(f"result path already exists: {output}")
    closure_path = ROOT / CLOSURE
    closure_data = closure_path.read_bytes()
    closure = json.loads(closure_data)
    if closure.get("schema") != 1 or closure.get("counts", {}).get(
        "identity_extension"
    ) != 56:
        raise ValueError("unexpected nonlinear verifier closure")
    if not runtime.is_file() or runtime.is_symlink():
        raise ValueError("parser runtime is not an ordinary file")

    capability, capability_seconds = _run_parser(
        runtime,
        runtime.parent,
        [flyspeck_parser_diagnostic.CAPABILITY_ARGUMENT],
        b"",
        timeout_seconds,
    )
    if (
        capability.returncode != 0
        or capability.stdout != flyspeck_parser_diagnostic.CAPABILITY_LINE
        or capability.stderr != b""
    ):
        raise ValueError("parser runtime capability handshake failed")

    attempts: list[dict[str, Any]] = []
    for index, identity in enumerate(closure["identity_extension"]):
        source_key = identity["source_key"]
        node = closure["source_nodes"][source_key]
        source_path = flyspeck_root / node["logical_relative_path"]
        source = source_path.read_bytes()
        if (
            len(source) != node["bytes"]
            or hashlib.md5(source, usedforsecurity=False).hexdigest()
            != node["md5"]
            or hashlib.sha256(source).hexdigest() != node["sha256"]
        ):
            raise ValueError(f"nonlinear verifier source identity drift: {source_key}")
        prepared, actions, unsupported, quotation = (
            flyspeck_parser_diagnostic.prepare_source(
                source_key,
                source,
                node["dependencies"],
                flyspeck_loader_quotation,
            )
        )
        if prepared is None or unsupported or quotation is None:
            raise ValueError(
                f"unsupported nonlinear verifier parser preparation: "
                f"{source_key}: {unsupported}"
            )
        nonce = os.urandom(32).hex()
        result, elapsed = _run_parser(
            runtime,
            runtime.parent,
            [flyspeck_parser_diagnostic.RUN_ARGUMENT, nonce],
            prepared,
            timeout_seconds,
        )
        protocol = flyspeck_parser_diagnostic.parse_protocol_result(
            nonce, result,
        )
        attempt = {
            "index": index,
            "source_key": source_key,
            "source": {
                "repository": node["repository"],
                "logical_relative_path": node["logical_relative_path"],
                "bytes": node["bytes"],
                "md5": node["md5"],
                "sha256": node["sha256"],
            },
            "manifest_action_count": len(actions),
            "quotation_expansion": quotation,
            "prepared_input": _record_bytes(prepared),
            "nonce": nonce,
            "elapsed_seconds": elapsed,
            "exit_code": result.returncode,
            "outcome": protocol["outcome"],
            "stdout": _record_bytes(result.stdout),
            "stderr": _record_bytes(result.stderr),
            "parser_error": protocol["controller_stderr_digest"],
        }
        attempts.append(attempt)
        print(
            f"{index + 1:02d}/56 {attempt['outcome']} "
            f"{elapsed:.3f}s {source_key}",
            flush=True,
        )

    outcome = (
        "parse-pass"
        if all(attempt["outcome"] == "parse-ok" for attempt in attempts)
        else "parse-failure"
    )
    payload = {
        "schema": RESULT_SCHEMA,
        "kind": "candle-flyspeck-nonlinear-verifier-parser-result",
        "status": "development-non-release",
        "claim": (
            "parser-only compatibility evidence; no inference, evaluation, "
            "proof, S2, S3, qualification, promotion, or release credit"
        ),
        "closure": {
            "path": CLOSURE.as_posix(),
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
        },
        "runtime": {
            "path": str(runtime),
            "bytes": runtime.stat().st_size,
            "sha256": _hash_file(runtime, "sha256"),
            "capability": flyspeck_parser_diagnostic.CAPABILITY_LINE.decode().rstrip(),
            "capability_seconds": capability_seconds,
        },
        "source_authority": closure["repositories"],
        "attempt_count": len(attempts),
        "parse_ok_count": sum(
            attempt["outcome"] == "parse-ok" for attempt in attempts
        ),
        "parse_error_count": sum(
            attempt["outcome"] != "parse-ok" for attempt in attempts
        ),
        "total_parser_seconds": sum(
            attempt["elapsed_seconds"] for attempt in attempts
        ),
        "outcome": outcome,
        "attempts": attempts,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x", encoding="utf-8") as destination:
        json.dump(payload, destination, indent=2, sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=180)
    arguments = parser.parse_args()
    payload = run(
        arguments.flyspeck_root,
        arguments.runtime,
        arguments.output,
        arguments.timeout_seconds,
    )
    if payload["outcome"] != "parse-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
