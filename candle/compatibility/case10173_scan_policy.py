#!/usr/bin/env python3
"""Turn staged case-10173 fixed-outer scans into an untrusted forest plan.

Parent, child, and optional depth-two verdicts are ordinary planning data.
The emitted ML is accepted only as input to the proof-producing reflected
forest replay, which rechecks every final cell and reconstructs every root.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Iterable

import case10173_parent_scan as parent_scan
import case10173_axis4_scan as axis4_scan


BRANCH_MARKER = "CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_BRANCH"
RESULT_MARKER = "CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_RESULT"
OK_MARKER = "CANDLE_CV_FIXED_OUTER_DEPTH2_SCAN_OK DEVELOPMENT_NON_RELEASE"
BRANCH_RE = re.compile(
    rf"{BRANCH_MARKER} label=(?P<label>\S+) index=(?P<index>\d+) "
    r"first_axis=(?P<first_axis>[1-6]) branch=(?P<branch>[01]) "
    r"flags=(?P<flags>[01](?:,[01]){11})"
)
RESULT_RE = re.compile(
    rf"{RESULT_MARKER} label=(?P<label>\S+) "
    r"branches=(?P<branches>\d+) verdicts=(?P<verdicts>\d+) "
    r"theorem_authority=none"
)


@dataclass(frozen=True)
class Depth2Verdict:
    label: str
    index: int
    first_axis: int
    branch: int
    flags: tuple[bool, ...]


@dataclass(frozen=True)
class RootPlan:
    index: int
    depth: int | None
    final_cells: int
    first_axis: int | None
    depth1_flags: tuple[bool, ...] | None
    depth2_axes: tuple[tuple[int, int | None], ...]


Work = tuple[int, int, int]


def _flags(text: str) -> tuple[bool, ...]:
    flags = tuple(value == "1" for value in text.split(","))
    if len(flags) != 12:
        raise ValueError(f"expected 12 depth-two flags, found {len(flags)}")
    return flags


def _pair(flags: tuple[bool, ...], axis: int) -> tuple[bool, bool]:
    if len(flags) != 12 or not 1 <= axis <= 6:
        raise ValueError("invalid child flag pair request")
    offset = 2 * (axis - 1)
    return flags[offset], flags[offset + 1]


def _viable_axes(flags: tuple[bool, ...]) -> list[int]:
    return [axis for axis in range(1, 7) if all(_pair(flags, axis))]


def _preferred_axis(axes: list[int]) -> int:
    if not axes:
        raise ValueError("cannot choose an axis from an empty set")
    return 4 if 4 in axes else axes[0]


def _best_first_axis(flags: tuple[bool, ...]) -> int:
    counts = {
        axis: sum(_pair(flags, axis))
        for axis in range(1, 7)
    }
    best = max(counts.values())
    return _preferred_axis([
        axis for axis in range(1, 7) if counts[axis] == best
    ])


def parse_depth2(line: str) -> Depth2Verdict:
    match = BRANCH_RE.search(line)
    if match is None:
        raise ValueError("line does not contain a depth-two branch record")
    return Depth2Verdict(
        label=match["label"],
        index=int(match["index"]),
        first_axis=int(match["first_axis"]),
        branch=int(match["branch"]),
        flags=_flags(match["flags"]),
    )


def read_depth2_logs(paths: Iterable[Path]) -> list[Depth2Verdict]:
    records: dict[Work, Depth2Verdict] = {}
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="strict")
        if OK_MARKER not in text:
            raise ValueError(f"incomplete depth-two log: {path}")
        local = [
            parse_depth2(line)
            for line in text.splitlines()
            if BRANCH_MARKER in line
        ]
        results = [
            match
            for line in text.splitlines()
            if (match := RESULT_RE.search(line)) is not None
        ]
        if len(results) != 1:
            raise ValueError(f"expected one depth-two result marker in {path}")
        result = results[0]
        if int(result["branches"]) != len(local):
            raise ValueError(f"depth-two branch count mismatch in {path}")
        if int(result["verdicts"]) != 12 * len(local):
            raise ValueError(f"depth-two verdict count mismatch in {path}")
        if any(record.label != result["label"] for record in local):
            raise ValueError(f"depth-two label mismatch in {path}")
        for record in local:
            key = (record.index, record.first_axis, record.branch)
            if key in records:
                raise ValueError(f"duplicate depth-two work item {key}")
            records[key] = record
    return [records[key] for key in sorted(records)]


def validate_child_scans(
    parents: list[parent_scan.RootVerdict],
    children: list[parent_scan.RootVerdict],
) -> None:
    rejected = [root.index for root in parents if not root.flags[0]]
    observed = [root.index for root in children]
    if observed != rejected:
        missing = sorted(set(rejected) - set(observed))
        unexpected = sorted(set(observed) - set(rejected))
        raise ValueError(
            f"child scan mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )
    if any(len(root.flags) != 13 for root in children):
        raise ValueError("child scan must contain parent plus twelve verdicts")
    if any(root.flags[0] for root in children):
        raise ValueError("child scan unexpectedly accepted a rejected parent")


def merge_axis4_child_scans(
    parents: list[parent_scan.RootVerdict],
    axis4_children: list[parent_scan.RootVerdict],
    fallback_children: list[parent_scan.RootVerdict],
) -> list[parent_scan.RootVerdict]:
    """Expand measured axis-4 closures and splice complete fallback scans.

    Unmeasured axes on an axis-4 closure are represented as false.  These
    flags are planning data only; the proof replay checks the selected axis-4
    cells from the original authenticated domains.
    """
    axis4_scan.validate_axis4_scans(parents, axis4_children)
    fallback = axis4_scan.fallback_indices(axis4_children)
    observed = [root.index for root in fallback_children]
    if observed != fallback:
        missing = sorted(set(fallback) - set(observed))
        unexpected = sorted(set(observed) - set(fallback))
        raise ValueError(
            f"all-axis fallback mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )
    if any(len(root.flags) != 13 for root in fallback_children):
        raise ValueError("all-axis fallback must contain thirteen verdicts")
    if any(root.flags[0] for root in fallback_children):
        raise ValueError("all-axis fallback unexpectedly accepted a parent")
    fallback_by_index = {root.index: root for root in fallback_children}
    merged: list[parent_scan.RootVerdict] = []
    for root in axis4_children:
        if root.index in fallback_by_index:
            merged.append(fallback_by_index[root.index])
            continue
        flags = [False] * 12
        flags[6:8] = root.flags[1:]
        merged.append(parent_scan.RootVerdict(
            label=f"{root.label}-normalized",
            index=root.index,
            flags=(False,) + tuple(flags),
        ))
    validate_child_scans(parents, merged)
    return merged


def required_depth2_work(
    children: list[parent_scan.RootVerdict],
) -> list[Work]:
    work: list[Work] = []
    for root in children:
        child_flags = root.flags[1:]
        if _viable_axes(child_flags):
            continue
        first_axis = _best_first_axis(child_flags)
        for branch, accepted in enumerate(_pair(child_flags, first_axis)):
            if not accepted:
                work.append((root.index, first_axis, branch))
    return work


def validate_depth2_work(
    records: list[Depth2Verdict], expected: list[Work],
) -> None:
    observed = [
        (record.index, record.first_axis, record.branch)
        for record in records
    ]
    if observed != expected:
        missing = sorted(set(expected) - set(observed))
        unexpected = sorted(set(observed) - set(expected))
        raise ValueError(
            f"depth-two scan mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )


def build_plans(
    parents: list[parent_scan.RootVerdict],
    children: list[parent_scan.RootVerdict],
    depth2: list[Depth2Verdict] = [],
) -> list[RootPlan]:
    validate_child_scans(parents, children)
    child_by_index = {root.index: root for root in children}
    depth2_by_key = {
        (record.index, record.first_axis, record.branch): record
        for record in depth2
    }
    plans: list[RootPlan] = []
    for parent in parents:
        if parent.flags[0]:
            plans.append(RootPlan(
                index=parent.index,
                depth=0,
                final_cells=1,
                first_axis=None,
                depth1_flags=None,
                depth2_axes=(),
            ))
            continue
        child = child_by_index[parent.index]
        child_flags = child.flags[1:]
        viable = _viable_axes(child_flags)
        if viable:
            plans.append(RootPlan(
                index=parent.index,
                depth=1,
                final_cells=2,
                first_axis=_preferred_axis(viable),
                depth1_flags=child.flags,
                depth2_axes=(),
            ))
            continue
        first_axis = _best_first_axis(child_flags)
        pair = _pair(child_flags, first_axis)
        selected: list[tuple[int, int | None]] = []
        for branch, accepted in enumerate(pair):
            if accepted:
                continue
            record = depth2_by_key.get((parent.index, first_axis, branch))
            axes = [] if record is None else _viable_axes(record.flags)
            selected.append((
                branch,
                None if not axes else _preferred_axis(axes),
            ))
        closed = all(axis is not None for _, axis in selected)
        plans.append(RootPlan(
            index=parent.index,
            depth=2 if closed else None,
            final_cells=(sum(pair) + 2 * len(selected)) if closed else 0,
            first_axis=first_axis,
            depth1_flags=child.flags,
            depth2_axes=tuple(selected),
        ))
    return plans


def unresolved_work(plans: list[RootPlan]) -> list[Work]:
    work: list[Work] = []
    for plan in plans:
        if plan.depth is not None:
            continue
        if plan.first_axis is None:
            raise ValueError(f"root {plan.index}: unresolved plan lacks axis")
        for branch, axis in plan.depth2_axes:
            if axis is None:
                work.append((plan.index, plan.first_axis, branch))
    return work


def work_chunks(work: list[Work], count: int) -> list[list[Work]]:
    if count <= 0:
        raise ValueError("depth-two chunk count must be positive")
    if len(work) < count:
        raise ValueError("more depth-two chunks than work items")
    return [
        work[(len(work) * offset) // count:
             (len(work) * (offset + 1)) // count]
        for offset in range(count)
    ]


def render_depth2_ml(work: list[Work], label: str) -> str:
    if not work:
        raise ValueError("depth-two work chunk is empty")
    entries = ";".join(
        f"({index},{axis},{branch})" for index, axis, branch in work
    )
    return (
        "(* Generated untrusted case-10173 depth-two scan work. *)\n"
        f'let candle_fixed_outer_depth2_scan_label = "{label}";;\n'
        f"let candle_fixed_outer_depth2_scan_work = [{entries}];;\n"
        'needs "candle/benchmark_cv_compute_analytic_expr_fixed_outer_depth2_scan.ml";;\n'
    )


def _render_plan(plan: RootPlan) -> str:
    leaf = "Candle_action296_forest_leaf"
    if plan.depth == 0:
        return leaf
    if plan.first_axis is None:
        raise ValueError(f"root {plan.index}: split plan lacks first axis")
    if plan.depth == 1:
        return f"Candle_action296_forest_split ({plan.first_axis},{leaf},{leaf})"
    if plan.depth != 2 or plan.depth1_flags is None:
        raise ValueError(f"root {plan.index}: unresolved plan cannot be rendered")
    axes = dict(plan.depth2_axes)
    pair = _pair(plan.depth1_flags[1:], plan.first_axis)
    rendered: list[str] = []
    for branch, accepted in enumerate(pair):
        if accepted:
            rendered.append(leaf)
            continue
        axis = axes.get(branch)
        if axis is None:
            raise ValueError(f"root {plan.index}: unresolved branch {branch}")
        rendered.append(
            f"Candle_action296_forest_split ({axis},{leaf},{leaf})"
        )
    return (
        f"Candle_action296_forest_split ({plan.first_axis},"
        f"{rendered[0]},{rendered[1]})"
    )


def render_policy_ml(
    plans: list[RootPlan], name: str, expected_digest: str | None = None,
) -> str:
    if not re.fullmatch(r"[a-z][a-z0-9_]*", name):
        raise ValueError("ML binding name must be lowercase alphanumeric/underscore")
    if expected_digest is not None and not re.fullmatch(
        r"[0-9a-f]{32}", expected_digest
    ):
        raise ValueError("expected theorem digest must be 32 lowercase hex digits")
    if any(plan.depth is None for plan in plans):
        raise ValueError("unresolved plan cannot be rendered")
    entries = [f"   ({plan.index},{_render_plan(plan)})" for plan in plans]
    digest = "None" if expected_digest is None else f'Some "{expected_digest}"'
    return (
        "(* Generated untrusted case-10173 fixed-outer forest plan.\n"
        "   The reflected proof adapter rechecks every selected cell. *)\n"
        "open Candle_cv_action296_adaptive_forest_prove;;\n"
        f"let {name}_roots =\n"
        + "[" + ";\n".join(entries) + "];;\n"
        + f"let {name}_final_cells = "
        + str(sum(plan.final_cells for plan in plans)) + ";;\n"
        + f"let {name}_expected_digest = {digest};;\n"
    )


def render_singleton_schedule_ml(plans: list[RootPlan]) -> str:
    if not plans or any(plan.depth is None for plan in plans):
        raise ValueError("singleton schedule requires a complete forest plan")
    sizes = ";".join("1" for _ in plans)
    return (
        "(* Generated conservative case-10173 fixed-outer group schedule.\n"
        "   Each singleton has the exact outer box used by policy discovery. *)\n"
        f"let candle_action296_generated_group_sizes = [{sizes}];;\n"
    )


def _identity(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def render_json(
    plans: list[RootPlan],
    parent_paths: list[Path],
    axis4_child_paths: list[Path],
    child_paths: list[Path],
    depth2_paths: list[Path],
) -> str:
    payload = {
        "schema": "candle-case10173-fixed-outer-forest-plan-v1",
        "status": "development-non-release",
        "claim": "untrusted plan only; reflected proof replay is authoritative",
        "inputs": {
            "parent_logs": [_identity(path) for path in parent_paths],
            "axis4_child_logs": [
                _identity(path) for path in axis4_child_paths
            ],
            "child_logs": [_identity(path) for path in child_paths],
            "depth2_logs": [_identity(path) for path in depth2_paths],
        },
        "summary": {
            "roots": len(plans),
            "direct": sum(plan.depth == 0 for plan in plans),
            "depth1": sum(plan.depth == 1 for plan in plans),
            "depth2": sum(plan.depth == 2 for plan in plans),
            "unresolved": sum(plan.depth is None for plan in plans),
            "final_cells": sum(plan.final_cells for plan in plans),
            "unresolved_work": unresolved_work(plans),
        },
        "plans": [asdict(plan) for plan in plans],
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-log", type=Path, action="append", required=True)
    parser.add_argument("--axis4-child-log", type=Path, action="append", default=[])
    parser.add_argument("--child-log", type=Path, action="append", default=[])
    parser.add_argument("--depth2-log", type=Path, action="append", default=[])
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-ml", type=Path)
    parser.add_argument("--output-schedule-ml", type=Path)
    parser.add_argument("--ml-name", default="candle_case10173_generated")
    parser.add_argument("--expected-digest")
    parser.add_argument("--output-depth2-ml", type=Path, action="append")
    args = parser.parse_args()

    parents = parent_scan.read_logs(args.parent_log)
    parent_scan.validate_parent_range(parents, args.start, args.stop)
    fallback_children = parent_scan.read_logs(args.child_log)
    if args.axis4_child_log:
        axis4_children = parent_scan.read_logs(args.axis4_child_log)
        children = merge_axis4_child_scans(
            parents, axis4_children, fallback_children,
        )
    else:
        children = fallback_children
        validate_child_scans(parents, children)
    depth2 = read_depth2_logs(args.depth2_log)
    expected_work = required_depth2_work(children)
    if args.depth2_log:
        validate_depth2_work(depth2, expected_work)
    plans = build_plans(parents, children, depth2)
    args.output_json.write_text(
        render_json(
            plans, args.parent_log, args.axis4_child_log,
            args.child_log, args.depth2_log,
        ),
        encoding="utf-8",
    )

    pending = unresolved_work(plans)
    if args.output_depth2_ml:
        chunks = work_chunks(pending, len(args.output_depth2_ml))
        for path, chunk in zip(args.output_depth2_ml, chunks, strict=True):
            first = chunk[0]
            last = chunk[-1]
            label = (
                f"case10173-depth2-{first[0]}-{first[1]}-{first[2]}-"
                f"{last[0]}-{last[1]}-{last[2]}"
            )
            path.write_text(render_depth2_ml(chunk, label), encoding="utf-8")
    if args.output_ml is not None:
        args.output_ml.write_text(
            render_policy_ml(
                plans, args.ml_name, expected_digest=args.expected_digest,
            ),
            encoding="utf-8",
        )
    if args.output_schedule_ml is not None:
        args.output_schedule_ml.write_text(
            render_singleton_schedule_ml(plans), encoding="utf-8",
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
