#!/usr/bin/env python3
"""Validate case-10173 parent scans and render rejected-root work.

The scan verdicts are untrusted policy data.  The generated ML selects work
for a later proof-producing replay and carries no theorem authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path
import re
from typing import Iterable


ROOT_MARKER = "CANDLE_CV_FIXED_OUTER_PARENT_SCAN_ROOT"
RESULT_MARKER = "CANDLE_CV_FIXED_OUTER_PARENT_SCAN_RESULT"
OK_MARKER = "CANDLE_CV_FIXED_OUTER_PARENT_SCAN_OK DEVELOPMENT_NON_RELEASE"
ROOT_RE = re.compile(
    rf"{ROOT_MARKER} label=(?P<label>\S+) index=(?P<index>\d+) "
    r"flags=(?P<flags>[01](?:,[01])*)"
)
RESULT_RE = re.compile(
    rf"{RESULT_MARKER} label=(?P<label>\S+) "
    r"roots=(?P<roots>\d+) verdicts=(?P<verdicts>\d+) "
    r"theorem_authority=none"
)


@dataclass(frozen=True)
class RootVerdict:
    label: str
    index: int
    flags: tuple[bool, ...]


def parse_root(line: str) -> RootVerdict:
    match = ROOT_RE.search(line)
    if match is None:
        raise ValueError("line does not contain a parent-scan root")
    return RootVerdict(
        label=match["label"],
        index=int(match["index"]),
        flags=tuple(value == "1" for value in match["flags"].split(",")),
    )


def read_logs(paths: Iterable[Path]) -> list[RootVerdict]:
    roots: dict[int, RootVerdict] = {}
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="strict")
        if OK_MARKER not in text:
            raise ValueError(f"incomplete parent-scan log: {path}")
        local = [
            parse_root(line)
            for line in text.splitlines()
            if ROOT_MARKER in line
        ]
        results = [
            match
            for line in text.splitlines()
            if (match := RESULT_RE.search(line)) is not None
        ]
        if len(results) != 1:
            raise ValueError(f"expected one result marker in {path}")
        result = results[0]
        if int(result["roots"]) != len(local):
            raise ValueError(f"root count mismatch in {path}")
        if int(result["verdicts"]) != sum(len(root.flags) for root in local):
            raise ValueError(f"verdict count mismatch in {path}")
        if any(root.label != result["label"] for root in local):
            raise ValueError(f"label mismatch in {path}")
        for root in local:
            if root.index in roots:
                raise ValueError(f"duplicate root index {root.index}")
            roots[root.index] = root
    return [roots[index] for index in sorted(roots)]


def validate_parent_range(
    roots: list[RootVerdict], start: int, stop: int,
) -> None:
    expected = list(range(start, stop + 1))
    observed = [root.index for root in roots]
    if observed != expected:
        missing = sorted(set(expected) - set(observed))
        unexpected = sorted(set(observed) - set(expected))
        raise ValueError(
            f"range mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )
    if any(len(root.flags) != 1 for root in roots):
        raise ValueError("parent-first scan contains child verdicts")


def _identity(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def render_json(roots: list[RootVerdict], paths: list[Path]) -> str:
    rejected = [root.index for root in roots if not root.flags[0]]
    payload = {
        "schema": "candle-case10173-parent-scan-v1",
        "status": "development-non-release",
        "claim": "untrusted plan only; proof-producing replay is authoritative",
        "logs": [_identity(path) for path in paths],
        "summary": {
            "roots": len(roots),
            "accepted": len(roots) - len(rejected),
            "rejected": len(rejected),
            "rejected_indices": rejected,
        },
        "records": [asdict(root) for root in roots],
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def render_ml_indices(indices: list[int], label: str) -> str:
    if not indices:
        raise ValueError("rejected-parent chunk is empty")
    encoded = ";".join(str(index) for index in indices)
    return (
        "(* Generated untrusted case-10173 rejected-parent scan. *)\n"
        "let candle_fixed_outer_parent_scan_label = "
        f'"{label}";;\n'
        f"let candle_fixed_outer_parent_scan_indices = [{encoded}];;\n"
        "let candle_fixed_outer_parent_scan_include_children = true;;\n"
        'needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_parent_scan.ml";;\n'
    )


def render_ml(roots: list[RootVerdict]) -> str:
    rejected = [root.index for root in roots if not root.flags[0]]
    if not rejected:
        raise ValueError("parent scan has no rejected roots to refine")
    return render_ml_indices(rejected, "case10173-rejected-parent-children")


def rejected_chunks(
    roots: list[RootVerdict], count: int,
) -> list[list[int]]:
    rejected = [root.index for root in roots if not root.flags[0]]
    if count <= 0:
        raise ValueError("rejected-parent chunk count must be positive")
    if len(rejected) < count:
        raise ValueError("more rejected-parent chunks than rejected roots")
    return [
        rejected[(len(rejected) * offset) // count:
                 (len(rejected) * (offset + 1)) // count]
        for offset in range(count)
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, action="append", required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-ml", type=Path, action="append", required=True)
    args = parser.parse_args()
    roots = read_logs(args.log)
    validate_parent_range(roots, args.start, args.stop)
    args.output_json.write_text(render_json(roots, args.log), encoding="utf-8")
    chunks = rejected_chunks(roots, len(args.output_ml))
    for path, chunk in zip(args.output_ml, chunks, strict=True):
        label = f"case10173-rejected-children-{chunk[0]}-{chunk[-1]}"
        path.write_text(render_ml_indices(chunk, label), encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
