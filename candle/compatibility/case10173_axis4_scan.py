#!/usr/bin/env python3
"""Validate axis-4-first case-10173 scans and render all-axis fallbacks.

Axis-4 verdicts are untrusted policy data.  Roots whose two axis-4 children
both accept need no further discovery; every other rejected parent is emitted
for the complete six-axis scan.  The later proof-producing replay remains the
sole theorem authority.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict
import hashlib
import json
from pathlib import Path

import case10173_parent_scan as parent_scan


def validate_axis4_scans(
    parents: list[parent_scan.RootVerdict],
    children: list[parent_scan.RootVerdict],
) -> None:
    rejected = [root.index for root in parents if not root.flags[0]]
    observed = [root.index for root in children]
    if observed != rejected:
        missing = sorted(set(rejected) - set(observed))
        unexpected = sorted(set(observed) - set(rejected))
        raise ValueError(
            f"axis-4 scan mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )
    if any(len(root.flags) != 3 for root in children):
        raise ValueError("axis-4 scan must contain parent plus two verdicts")
    if any(root.flags[0] for root in children):
        raise ValueError("axis-4 scan unexpectedly accepted a rejected parent")


def fallback_indices(children: list[parent_scan.RootVerdict]) -> list[int]:
    return [root.index for root in children if not all(root.flags[1:])]


def chunks(values: list[int], count: int) -> list[list[int]]:
    if count <= 0:
        raise ValueError("fallback chunk count must be positive")
    if len(values) < count:
        raise ValueError("more fallback chunks than roots")
    return [
        values[(len(values) * offset) // count:
               (len(values) * (offset + 1)) // count]
        for offset in range(count)
    ]


def _identity(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def render_json(
    children: list[parent_scan.RootVerdict], paths: list[Path],
) -> str:
    fallback = fallback_indices(children)
    payload = {
        "schema": "candle-case10173-axis4-scan-v1",
        "status": "development-non-release",
        "claim": "untrusted plan only; proof-producing replay is authoritative",
        "logs": [_identity(path) for path in paths],
        "summary": {
            "rejected_parents": len(children),
            "axis4_closed": len(children) - len(fallback),
            "all_axis_fallback": len(fallback),
            "fallback_indices": fallback,
        },
        "records": [asdict(root) for root in children],
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-log", type=Path, action="append", required=True)
    parser.add_argument("--axis4-log", type=Path, action="append", required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-ml", type=Path, action="append", default=[])
    args = parser.parse_args()

    parents = parent_scan.read_logs(args.parent_log)
    parent_scan.validate_parent_range(parents, args.start, args.stop)
    children = parent_scan.read_logs(args.axis4_log)
    validate_axis4_scans(parents, children)
    fallback = fallback_indices(children)
    args.output_json.write_text(
        render_json(children, args.axis4_log), encoding="utf-8",
    )
    if bool(fallback) != bool(args.output_ml):
        raise ValueError(
            "fallback outputs are required exactly when fallback work exists"
        )
    work_chunks = chunks(fallback, len(args.output_ml)) if fallback else []
    for path, chunk in zip(args.output_ml, work_chunks, strict=True):
        label = f"case10173-all-axis-fallback-{chunk[0]}-{chunk[-1]}"
        path.write_text(
            parent_scan.render_ml_indices(chunk, label), encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
