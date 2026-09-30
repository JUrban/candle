#!/usr/bin/env python3
"""Validate the retained complete reflected proof for nonlinear case 16594.

This checker is DEVELOPMENT / NON-RELEASE infrastructure.  The HOL driver
itself checks the root theorem, assumptions, and axiom set.  This postflight
adds an independent check that every bounded streaming segment completed in
order and that the retained inputs and terminal markers are unchanged.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


SEGMENTS = 219
NUMERICAL_CELLS = 875
AUTHENTICATED_LEAVES = 860
GLUE_NODES = 874
TOKEN_ITEMS = NUMERICAL_CELLS + GLUE_NODES
THEOREM_DIGEST = "8bb2c1bf3d1c1944d497c0da68b88207"
WRAPPER_SHA256 = "1dfe5868225a37afc8c345e07c974b9fc4b2df5c710dfc90fac54517998c3426"
PROOF_SOURCE_SHA256 = "52db0358ae62fac03ce0cf0b44afbec35a23bbe46734967b31dcb85d2f50240d"
SUPPORT_CHECKPOINT_SHA256 = (
    "579ed76c80e0fce59bab0b2989d43b5349ed6671d35f28f2c1d9f989c1691589"
)

BEGIN_RE = re.compile(
    r"^CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK "
    r"event=begin index=(?P<index>\d+) total=(?P<total>\d+) "
    r"cells=(?P<cells>\d+)$"
)
END_RE = re.compile(
    r"^CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK "
    r"event=end index=(?P<index>\d+) total=(?P<total>\d+) "
    r"cells=(?P<cells>\d+) token_items=(?P<token_items>\d+) "
    r"active_roots=(?P<active_roots>\d+)$"
)
RESULT_RE = re.compile(
    r"^CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_RESULT "
    r"authenticated_leaves=(?P<authenticated_leaves>\d+) "
    r"numerical_cells=(?P<numerical_cells>\d+) "
    r"glue_nodes=(?P<glue_nodes>\d+) "
    r"numerical_computes=(?P<numerical_computes>\d+) "
    r"topology_segments=(?P<topology_segments>\d+) "
    r"root_handoffs=(?P<root_handoffs>\d+) "
    r"assumptions=(?P<assumptions>\d+) "
    r"theorem_digest=(?P<theorem_digest>[0-9a-f]{32})$"
)
OK_MARKER = (
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_OK "
    "DEVELOPMENT_NON_RELEASE"
)
SOURCE_ERROR_RE = re.compile(
    r"ERROR:|EXCEPTION:|Parsing failed|Program exited"
)
HASH_RE = re.compile(r"^(?P<sha256>[0-9a-f]{64})  (?P<path>.+)$")


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def _identity(path: Path) -> dict[str, object]:
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"missing ordinary artifact: {path}")
    return {
        "path": str(path.resolve()),
        "bytes": path.stat().st_size,
        "sha256": _sha256(path),
    }


def _manifest_records(path: Path) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    seen: set[Path] = set()
    text = path.read_text(encoding="utf-8", errors="strict")
    for line in text.splitlines():
        match = HASH_RE.fullmatch(line)
        if match is None:
            raise ValueError(f"malformed SHA-256 manifest line in {path}")
        target = Path(match["path"])
        if not target.is_absolute():
            target = path.parent / target
        if target.is_symlink() or not target.is_file():
            raise ValueError(f"manifest target is not an ordinary file: {target}")
        resolved = target.resolve()
        if resolved in seen:
            raise ValueError(f"duplicate manifest target: {resolved}")
        seen.add(resolved)
        observed = _sha256(target)
        if observed != match["sha256"]:
            raise ValueError(f"SHA-256 mismatch: {target}")
        records.append({
            "path": str(resolved),
            "bytes": target.stat().st_size,
            "sha256": observed,
        })
    if not records:
        raise ValueError(f"empty SHA-256 manifest: {path}")
    return records


def _single_hash_manifest(path: Path) -> dict[str, object]:
    records = _manifest_records(path)
    if len(records) != 1:
        raise ValueError(f"expected one SHA-256 record in {path}")
    return records[0]


def _marker_fragment(line: str, marker: str) -> str | None:
    where = line.find(marker)
    if where < 0:
        return None
    return line[where:].strip()


def parse_completed_log(text: str, ready_marker: str) -> dict[str, object]:
    """Check ordered streaming markers and return their exact totals."""
    if SOURCE_ERROR_RE.search(text):
        raise ValueError("source/runtime error marker in completed log")

    next_index = 0
    pending: tuple[int, int] | None = None
    cell_total = 0
    token_total = 0
    final_active_roots: int | None = None
    result: dict[str, object] | None = None
    result_line: int | None = None
    ok_line: int | None = None
    ready_line: int | None = None

    begin_marker = "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK event=begin"
    end_marker = "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK event=end"
    result_marker = "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_RESULT"

    for line_number, line in enumerate(text.splitlines(), 1):
        fragment = _marker_fragment(line, begin_marker)
        if fragment is not None:
            match = BEGIN_RE.fullmatch(fragment)
            if match is None:
                raise ValueError(f"malformed begin marker at line {line_number}")
            index = int(match["index"])
            total = int(match["total"])
            cells = int(match["cells"])
            expected_cells = 3 if index == SEGMENTS - 1 else 4
            if pending is not None or index != next_index:
                raise ValueError(f"out-of-order begin marker at line {line_number}")
            if total != SEGMENTS or cells != expected_cells:
                raise ValueError(f"begin contract mismatch at line {line_number}")
            pending = (index, cells)
            continue

        fragment = _marker_fragment(line, end_marker)
        if fragment is not None:
            match = END_RE.fullmatch(fragment)
            if match is None:
                raise ValueError(f"malformed end marker at line {line_number}")
            index = int(match["index"])
            total = int(match["total"])
            cells = int(match["cells"])
            token_items = int(match["token_items"])
            active_roots = int(match["active_roots"])
            if pending != (index, cells) or index != next_index:
                raise ValueError(f"unmatched end marker at line {line_number}")
            if total != SEGMENTS or token_items < cells or active_roots <= 0:
                raise ValueError(f"end contract mismatch at line {line_number}")
            cell_total += cells
            token_total += token_items
            final_active_roots = active_roots
            next_index += 1
            pending = None
            continue

        fragment = _marker_fragment(line, result_marker)
        if fragment is not None:
            match = RESULT_RE.fullmatch(fragment)
            if match is None or result is not None:
                raise ValueError(f"malformed or duplicate result at line {line_number}")
            result = {
                key: (value if key == "theorem_digest" else int(value))
                for key, value in match.groupdict().items()
            }
            result_line = line_number

        if OK_MARKER in line:
            if line.strip() != OK_MARKER or ok_line is not None:
                raise ValueError(f"malformed or duplicate OK marker at line {line_number}")
            ok_line = line_number

        if ready_marker in line:
            if line.strip() != ready_marker or ready_line is not None:
                raise ValueError(f"malformed or duplicate ready marker at line {line_number}")
            ready_line = line_number

    if pending is not None or next_index != SEGMENTS:
        raise ValueError(f"incomplete segment stream: closed {next_index}/{SEGMENTS}")
    if cell_total != NUMERICAL_CELLS or token_total != TOKEN_ITEMS:
        raise ValueError("stream aggregate mismatch")
    if final_active_roots != 1:
        raise ValueError("final compact stack did not contain exactly one root")
    expected_result = {
        "authenticated_leaves": AUTHENTICATED_LEAVES,
        "numerical_cells": NUMERICAL_CELLS,
        "glue_nodes": GLUE_NODES,
        "numerical_computes": SEGMENTS,
        "topology_segments": SEGMENTS,
        "root_handoffs": 1,
        "assumptions": 0,
        "theorem_digest": THEOREM_DIGEST,
    }
    if result != expected_result:
        raise ValueError("terminal theorem result mismatch")
    if None in (result_line, ok_line, ready_line) or not (
        result_line < ok_line < ready_line
    ):
        raise ValueError("terminal marker ordering mismatch")
    return {
        "segments": next_index,
        "numerical_cells": cell_total,
        "token_items": token_total,
        "final_active_roots": final_active_roots,
        "result": result,
        "result_line": result_line,
        "ok_line": ok_line,
        "ready_line": ready_line,
    }


def _validate_sealed_run(
    directory: Path,
    expected_ready_marker: str,
) -> dict[str, object]:
    if not (directory / "CHECKPOINT-READY").is_file():
        raise ValueError(f"run is not checkpoint-ready: {directory}")
    if (directory / "CHECKPOINT-FAILED").exists():
        raise ValueError(f"run has a checkpoint failure marker: {directory}")
    receipt_text = (directory / "checkpoint-seal.receipt").read_text(
        encoding="utf-8", errors="strict"
    )
    receipt = dict(
        line.split("=", 1) for line in receipt_text.splitlines() if "=" in line
    )
    if receipt.get("ready_marker") != expected_ready_marker:
        raise ValueError(f"checkpoint ready-marker mismatch: {directory}")
    checkpoint = _single_hash_manifest(directory / "checkpoint.sha256")
    base_log = _single_hash_manifest(directory / "base-log.sha256")
    return {
        "directory": str(directory.resolve()),
        "checkpoint": checkpoint,
        "base_log": base_log,
        "seal_receipt": _identity(directory / "checkpoint-seal.receipt"),
        "fragments": _manifest_records(directory / "fragments.sha256"),
        "inputs": _manifest_records(directory / "input-files.sha256"),
    }


def validate(
    run: Path,
    support: Path,
    ready_marker: str,
    support_ready_marker: str,
) -> dict[str, object]:
    run = run.resolve()
    support = support.resolve()
    run_evidence = _validate_sealed_run(run, ready_marker)
    support_evidence = _validate_sealed_run(support, support_ready_marker)

    run_fragment_hashes = {item["sha256"] for item in run_evidence["fragments"]}
    support_fragment_hashes = {
        item["sha256"] for item in support_evidence["fragments"]
    }
    if run_fragment_hashes != {WRAPPER_SHA256}:
        raise ValueError("complete-run wrapper identity mismatch")
    if support_fragment_hashes != {PROOF_SOURCE_SHA256}:
        raise ValueError("support proof-source identity mismatch")
    if support_evidence["checkpoint"]["sha256"] != SUPPORT_CHECKPOINT_SHA256:
        raise ValueError("support checkpoint identity mismatch")
    run_input_hashes = {item["sha256"] for item in run_evidence["inputs"]}
    if SUPPORT_CHECKPOINT_SHA256 not in run_input_hashes:
        raise ValueError("complete run was not derived from the approved support checkpoint")
    if WRAPPER_SHA256 not in run_input_hashes:
        raise ValueError("complete run input manifest omits the approved wrapper")

    log_path = run / "base.log"
    stream = parse_completed_log(
        log_path.read_text(encoding="utf-8", errors="strict"), ready_marker
    )
    return {
        "schema": "candle-case16594-compact-stream-postflight-v1",
        "status": "development-non-release",
        "claim": "retained-run validation only; no release authority",
        "validator": _identity(Path(__file__)),
        "run": run_evidence,
        "support": support_evidence,
        "stream": stream,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--support", type=Path, required=True)
    parser.add_argument("--ready-marker", required=True)
    parser.add_argument("--support-ready-marker", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    payload = validate(
        args.run,
        args.support,
        args.ready_marker,
        args.support_ready_marker,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(args.output.suffix + ".tmp")
    temporary.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(args.output)
    print(
        "CANDLE_CV_CASE16594_COMPACT_STREAM_POSTFLIGHT_OK "
        f"segments={SEGMENTS} numerical_cells={NUMERICAL_CELLS} "
        f"token_items={TOKEN_ITEMS} theorem_digest={THEOREM_DIGEST}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
