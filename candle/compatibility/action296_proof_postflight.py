#!/usr/bin/env python3
"""Validate completed action-296 sequential and grouped proof runs.

This is a DEVELOPMENT / NON-RELEASE evidence checker.  It does not grant
proof authority: it authenticates the retained run files and checks that the
kernel-producing drivers reached their exact terminal contracts.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re

import action296_group_schedule


SEQUENTIAL_MARKER = "CANDLE_CV_ACTION296_POLICY_ADAPTIVE_PROOF_RESULT"
SEQUENTIAL_OK = (
    "CANDLE_CV_ACTION296_POLICY_ADAPTIVE_PROOF_OK "
    "DEVELOPMENT_NON_RELEASE"
)
SEQUENTIAL_RE = re.compile(
    rf"^{SEQUENTIAL_MARKER} "
    r"original_leaves=(?P<original_leaves>\d+) "
    r"final_cells=(?P<final_cells>\d+) "
    r"theorem_digest=(?P<theorem_digest>[0-9a-f]{32})$"
)
SOURCE_ERROR_RE = re.compile(r"ERROR:|EXCEPTION:|Parsing failed")
HASH_RE = re.compile(r"^(?P<sha256>[0-9a-f]{64})  (?P<path>.+)$")

STOP_KEYS = {
    "sequential": (
        "action296-adaptive-forest-proof/forest/sequential-forest"
    ),
    "grouped": (
        "action296-bounded-grouped-forest-proof/forest/bounded-forest"
    ),
}


@dataclass(frozen=True)
class ProofResult:
    mode: str
    original_leaves: int
    final_cells: int
    theorem_digest: str
    attempts: int | None = None
    successful_groups: int | None = None
    group_sizes: tuple[int, ...] | None = None


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _identity(path: Path) -> dict[str, object]:
    if not path.is_file():
        raise ValueError(f"missing ordinary artifact: {path}")
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": _sha256(path),
    }


def _read_key_values(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8", errors="strict").splitlines():
        if not line or "=" not in line:
            raise ValueError(f"malformed key/value line in {path}: {line!r}")
        key, value = line.split("=", 1)
        if not key or key in values:
            raise ValueError(f"duplicate or empty key in {path}: {key!r}")
        values[key] = value
    return values


def _manifest_records(path: Path) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    seen: set[Path] = set()
    for line in path.read_text(encoding="utf-8", errors="strict").splitlines():
        match = HASH_RE.fullmatch(line)
        if match is None:
            raise ValueError(f"malformed SHA-256 manifest line in {path}")
        target = Path(match["path"])
        if not target.is_absolute():
            target = path.parent / target
        resolved = target.resolve()
        if resolved in seen:
            raise ValueError(f"duplicate manifest target: {resolved}")
        seen.add(resolved)
        observed = _sha256(resolved)
        if observed != match["sha256"]:
            raise ValueError(f"SHA-256 mismatch: {resolved}")
        records.append({
            "path": str(resolved),
            "bytes": resolved.stat().st_size,
            "sha256": observed,
        })
    if not records:
        raise ValueError(f"empty SHA-256 manifest: {path}")
    return records


def _validate_acknowledgement(run: Path) -> dict[str, object]:
    fragments = run / "fragments.sha256"
    started_path = run / "input-ack.started"
    receipt_path = run / "input-ack.receipt"
    started = _read_key_values(started_path)
    receipt = _read_key_values(receipt_path)
    for key in ("nonce", "fragment_set_sha256"):
        if not started.get(key) or receipt.get(key) != started[key]:
            raise ValueError(f"input acknowledgement mismatch: {key}")
    if started["fragment_set_sha256"] != _sha256(fragments):
        raise ValueError("input acknowledgement fragment-set hash mismatch")
    try:
        ack_line = int(receipt["ack_line"])
        marker_line = int(receipt["marker_line"])
    except (KeyError, ValueError) as error:
        raise ValueError("malformed acknowledgement line positions") from error
    if ack_line <= 0 or marker_line <= ack_line:
        raise ValueError("invalid acknowledgement/marker ordering")
    return {
        "started": _identity(started_path),
        "receipt": _identity(receipt_path),
        "nonce": started["nonce"],
        "fragment_set_sha256": started["fragment_set_sha256"],
        "ack_line": ack_line,
        "marker_line": marker_line,
    }


def _validate_profile(run: Path, mode: str) -> dict[str, object]:
    path = run / "phase-profile.json"
    profile = json.loads(path.read_text(encoding="utf-8", errors="strict"))
    if profile.get("schema") != "candle-certificate-phase-profile-v1":
        raise ValueError(f"unexpected phase-profile schema: {path}")
    if Path(str(profile.get("log"))).resolve() != (run / "candle.log").resolve():
        raise ValueError(f"phase-profile log identity mismatch: {path}")
    if profile.get("stop_key") != STOP_KEYS[mode]:
        raise ValueError(f"phase-profile stop key mismatch: {path}")
    if profile.get("stop_seen") is not True:
        raise ValueError(f"phase-profile did not see terminal phase: {path}")
    if profile.get("unclosed_phases") != []:
        raise ValueError(f"phase-profile contains unclosed phases: {path}")
    if not isinstance(profile.get("events"), list) or not profile["events"]:
        raise ValueError(f"phase-profile has no events: {path}")
    if not isinstance(profile.get("phases"), list) or not profile["phases"]:
        raise ValueError(f"phase-profile has no closed phases: {path}")
    return {
        "artifact": _identity(path),
        "duration_seconds": profile.get("duration_seconds"),
        "peak_sampled_rss_kib": profile.get("peak_sampled_rss_kib"),
        "events": len(profile["events"]),
        "phases": len(profile["phases"]),
        "stop_key": profile["stop_key"],
    }


def _sequential_result(log: Path) -> ProofResult:
    text = log.read_text(encoding="utf-8", errors="strict")
    if SOURCE_ERROR_RE.search(text):
        raise ValueError(f"source error in completed log: {log}")
    if sum(SEQUENTIAL_OK in line for line in text.splitlines()) != 1:
        raise ValueError(f"missing or duplicate sequential OK marker: {log}")
    matches = []
    for line in text.splitlines():
        where = line.find(SEQUENTIAL_MARKER)
        if where >= 0:
            match = SEQUENTIAL_RE.fullmatch(line[where:].strip())
            if match is None:
                raise ValueError(f"malformed sequential result: {line}")
            matches.append(match)
    if len(matches) != 1:
        raise ValueError(f"expected one sequential result, found {len(matches)}")
    match = matches[0]
    return ProofResult(
        mode="sequential",
        original_leaves=int(match["original_leaves"]),
        final_cells=int(match["final_cells"]),
        theorem_digest=match["theorem_digest"],
    )


def _grouped_result(log: Path) -> ProofResult:
    text = log.read_text(encoding="utf-8", errors="strict")
    if SOURCE_ERROR_RE.search(text):
        raise ValueError(f"source error in completed log: {log}")
    grouped = action296_group_schedule.read_schedule(log)
    return ProofResult(
        mode="grouped",
        original_leaves=grouped.original_leaves,
        final_cells=grouped.final_cells,
        theorem_digest=grouped.theorem_digest,
        attempts=grouped.attempts,
        successful_groups=grouped.successful_groups,
        group_sizes=grouped.group_sizes,
    )


def validate_run(
    run: Path,
    mode: str,
    expected_roots: int,
    expected_cells: int,
    expected_digest: str | None,
) -> dict[str, object]:
    run = run.resolve()
    log = run / "candle.log"
    result = (
        _sequential_result(log)
        if mode == "sequential"
        else _grouped_result(log)
    )
    if result.original_leaves != expected_roots:
        raise ValueError(f"{mode} root count mismatch")
    if result.final_cells != expected_cells:
        raise ValueError(f"{mode} final-cell count mismatch")
    if expected_digest is not None and result.theorem_digest != expected_digest:
        raise ValueError(f"{mode} theorem digest mismatch")

    result_manifest = run / "result-files.sha256"
    result_records = _manifest_records(result_manifest)
    required = {
        (run / name).resolve()
        for name in ("fragments.sha256", "stdin.ml", "candle.log")
    }
    observed = {Path(str(record["path"])) for record in result_records}
    if observed != required:
        raise ValueError(f"{mode} result-file manifest membership mismatch")

    return {
        "run": str(run),
        "mode": mode,
        "result": asdict(result),
        "artifacts": {
            "log": _identity(log),
            "stdin": _identity(run / "stdin.ml"),
            "fragments_manifest": _identity(run / "fragments.sha256"),
            "result_manifest": _identity(result_manifest),
            "result_files": result_records,
            "fragments": _manifest_records(run / "fragments.sha256"),
        },
        "input_acknowledgement": _validate_acknowledgement(run),
        "phase_profile": _validate_profile(run, mode),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--sequential-run", type=Path)
    parser.add_argument("--grouped-run", type=Path)
    parser.add_argument("--expected-roots", type=int, required=True)
    parser.add_argument("--expected-cells", type=int, required=True)
    parser.add_argument("--expected-digest")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.sequential_run is None and args.grouped_run is None:
        parser.error("at least one completed run is required")
    if args.expected_roots <= 0 or args.expected_cells < args.expected_roots:
        parser.error("invalid expected root/final-cell counts")
    if args.expected_digest is not None and not re.fullmatch(
        r"[0-9a-f]{32}", args.expected_digest
    ):
        parser.error("expected digest must be 32 lowercase hexadecimal digits")

    runs = []
    if args.sequential_run is not None:
        runs.append(validate_run(
            args.sequential_run,
            "sequential",
            args.expected_roots,
            args.expected_cells,
            args.expected_digest,
        ))
    if args.grouped_run is not None:
        runs.append(validate_run(
            args.grouped_run,
            "grouped",
            args.expected_roots,
            args.expected_cells,
            args.expected_digest,
        ))
    if len(runs) == 2:
        left = runs[0]["result"]
        right = runs[1]["result"]
        for key in ("original_leaves", "final_cells", "theorem_digest"):
            if left[key] != right[key]:
                raise ValueError(f"sequential/grouped {key} mismatch")

    payload = {
        "schema": "candle-action296-proof-postflight-v1",
        "status": "development-non-release",
        "claim": "retained-run validation only; no release authority",
        "validator": _identity(Path(__file__)),
        "expected": {
            "roots": args.expected_roots,
            "final_cells": args.expected_cells,
            "theorem_digest": args.expected_digest,
        },
        "runs": runs,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(args.output)
    print(
        "CANDLE_CV_ACTION296_POSTFLIGHT_OK "
        f"runs={len(runs)} roots={args.expected_roots} "
        f"final_cells={args.expected_cells} "
        f"theorem_digest={runs[0]['result']['theorem_digest']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
