#!/usr/bin/env python3
"""Validate action-296 discovery logs and render untrusted forest plans.

The emitted plans carry no proof authority.  They are inputs to the generic
adaptive-forest proof adapter, which must recompute every selected final cell
and reconstruct each original Flyspeck root.
"""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
import re
from typing import Iterable


LEAF_MARKER = "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF"
OK_MARKER = "CANDLE_CV_ACTION296_CHUNK_SCAN_OK DEVELOPMENT_NON_RELEASE"
LEAF_RE = re.compile(
    rf"^{LEAF_MARKER} label=(?P<label>\S+) index=(?P<index>\d+) "
    r"depth=(?P<depth>0|1|2|unresolved) "
    r"final_cells=(?P<final_cells>\d+) "
    r"first_axis=(?P<first_axis>none|[1-6]) "
    r"depth1_flags=(?P<depth1_flags>[01](?:,[01]){12}) "
    r"depth2=(?P<depth2>.*)$"
)
BRANCH_RE = re.compile(
    r"^(?P<branch>[01]):(?P<axis>none|[1-6]):"
    r"(?P<flags>[01](?:,[01]){11})$"
)


@dataclass(frozen=True)
class Branch:
    branch: int
    selected_axis: int | None
    flags: tuple[bool, ...]


@dataclass(frozen=True)
class Leaf:
    label: str
    index: int
    depth: int | None
    final_cells: int
    first_axis: int | None
    depth1_flags: tuple[bool, ...]
    depth2: tuple[Branch, ...]


def _flags(text: str, expected: int) -> tuple[bool, ...]:
    result = tuple(value == "1" for value in text.split(","))
    if len(result) != expected:
        raise ValueError(f"expected {expected} flags, found {len(result)}")
    return result


def _pair(flags: tuple[bool, ...], axis: int) -> tuple[bool, bool]:
    offset = 2 * (axis - 1)
    return flags[offset], flags[offset + 1]


def _viable_axes(flags: tuple[bool, ...]) -> list[int]:
    return [axis for axis in range(1, 7) if all(_pair(flags, axis))]


def parse_leaf(line: str) -> Leaf:
    where = line.find(LEAF_MARKER)
    if where < 0:
        raise ValueError("line does not contain a chunk leaf marker")
    match = LEAF_RE.fullmatch(line[where:].strip())
    if match is None:
        raise ValueError(f"malformed chunk leaf record: {line.rstrip()}")
    depth_text = match["depth"]
    depth = None if depth_text == "unresolved" else int(depth_text)
    first_axis = (
        None if match["first_axis"] == "none"
        else int(match["first_axis"])
    )
    branches: list[Branch] = []
    depth2_text = match["depth2"]
    if depth2_text:
        for encoded in depth2_text.split(";"):
            branch_match = BRANCH_RE.fullmatch(encoded)
            if branch_match is None:
                raise ValueError(f"malformed depth-two branch: {encoded}")
            branches.append(Branch(
                branch=int(branch_match["branch"]),
                selected_axis=(
                    None if branch_match["axis"] == "none"
                    else int(branch_match["axis"])
                ),
                flags=_flags(branch_match["flags"], 12),
            ))
    leaf = Leaf(
        label=match["label"],
        index=int(match["index"]),
        depth=depth,
        final_cells=int(match["final_cells"]),
        first_axis=first_axis,
        depth1_flags=_flags(match["depth1_flags"], 13),
        depth2=tuple(branches),
    )
    validate_leaf(leaf)
    return leaf


def validate_leaf(leaf: Leaf) -> None:
    parent = leaf.depth1_flags[0]
    children = leaf.depth1_flags[1:]
    viable = _viable_axes(children)
    branch_numbers = [branch.branch for branch in leaf.depth2]
    if branch_numbers != sorted(set(branch_numbers)):
        raise ValueError(f"leaf {leaf.index}: duplicate or unordered branches")
    if leaf.depth == 0:
        if not parent or leaf.first_axis is not None or leaf.depth2:
            raise ValueError(f"leaf {leaf.index}: invalid direct policy")
        if leaf.final_cells != 1:
            raise ValueError(f"leaf {leaf.index}: direct cell count")
        return
    if parent:
        raise ValueError(f"leaf {leaf.index}: split accepted parent")
    if leaf.first_axis is None:
        raise ValueError(f"leaf {leaf.index}: split without first axis")
    left, right = _pair(children, leaf.first_axis)
    if leaf.depth == 1:
        if leaf.first_axis not in viable or leaf.depth2:
            raise ValueError(f"leaf {leaf.index}: invalid depth-one policy")
        if leaf.final_cells != 2:
            raise ValueError(f"leaf {leaf.index}: depth-one cell count")
        return
    if viable:
        raise ValueError(f"leaf {leaf.index}: unnecessary depth-two policy")
    rejected = [branch for branch, accepted in enumerate((left, right))
                if not accepted]
    if branch_numbers != rejected:
        raise ValueError(
            f"leaf {leaf.index}: depth-two branch set {branch_numbers} "
            f"does not match rejected children {rejected}"
        )
    branch_closed = [
        branch.selected_axis is not None
        and branch.selected_axis in _viable_axes(branch.flags)
        for branch in leaf.depth2
    ]
    if leaf.depth == 2:
        if not all(branch_closed):
            raise ValueError(f"leaf {leaf.index}: unclosed depth-two branch")
        expected_cells = int(left) + int(right) + 2 * len(rejected)
        if leaf.final_cells != expected_cells:
            raise ValueError(f"leaf {leaf.index}: depth-two cell count")
    elif leaf.depth is None:
        if all(branch_closed) or leaf.final_cells != 0:
            raise ValueError(f"leaf {leaf.index}: invalid unresolved policy")
    else:
        raise ValueError(f"leaf {leaf.index}: unsupported depth {leaf.depth}")


def read_logs(paths: Iterable[Path], require_complete: bool = True) -> list[Leaf]:
    leaves: dict[int, Leaf] = {}
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="strict")
        if require_complete and OK_MARKER not in text:
            raise ValueError(f"incomplete chunk log: {path}")
        for line in text.splitlines():
            if LEAF_MARKER not in line:
                continue
            leaf = parse_leaf(line)
            if leaf.index in leaves:
                raise ValueError(f"duplicate leaf index {leaf.index}")
            leaves[leaf.index] = leaf
    return [leaves[index] for index in sorted(leaves)]


def validate_range(leaves: list[Leaf], start: int, stop: int) -> None:
    expected = list(range(start, stop + 1))
    observed = [leaf.index for leaf in leaves]
    if observed != expected:
        missing = sorted(set(expected) - set(observed))
        unexpected = sorted(set(observed) - set(expected))
        raise ValueError(
            f"range mismatch: missing={missing[:20]} "
            f"unexpected={unexpected[:20]}"
        )


def _plan(leaf: Leaf) -> str:
    base = "Candle_action296_forest_leaf"
    if leaf.depth == 0:
        return base
    if leaf.depth == 1:
        return (
            f"Candle_action296_forest_split "
            f"({leaf.first_axis},{base},{base})"
        )
    if leaf.depth != 2:
        raise ValueError(f"leaf {leaf.index}: unresolved plan cannot be rendered")
    branches = {branch.branch: branch for branch in leaf.depth2}
    children = leaf.depth1_flags[1:]
    rendered: list[str] = []
    for branch, accepted in enumerate(_pair(children, leaf.first_axis or 0)):
        if accepted:
            rendered.append(base)
        else:
            axis = branches[branch].selected_axis
            if axis is None:
                raise ValueError(f"leaf {leaf.index}: unresolved branch")
            rendered.append(
                f"Candle_action296_forest_split ({axis},{base},{base})"
            )
    return (
        f"Candle_action296_forest_split "
        f"({leaf.first_axis},{rendered[0]},{rendered[1]})"
    )


def render_ml(leaves: list[Leaf], name: str) -> str:
    if not re.fullmatch(r"[a-z][a-z0-9_]*", name):
        raise ValueError("ML binding name must be lowercase alphanumeric/underscore")
    entries = [f"   ({leaf.index},{_plan(leaf)})" for leaf in leaves]
    total_cells = sum(leaf.final_cells for leaf in leaves)
    return (
        "(* Generated untrusted action-296 forest plan.  The reflected proof\n"
        "   adapter must recheck every selected final cell. *)\n"
        f"let {name}_roots =\n"
        + "[" + ";\n".join(entries) + "];;\n"
        + f"let {name}_final_cells = {total_cells};;\n"
    )


def _identity(path: Path) -> dict[str, object]:
    data = path.read_bytes()
    return {
        "path": str(path.resolve()),
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def render_json(leaves: list[Leaf], paths: list[Path]) -> str:
    payload = {
        "schema": "candle-action296-untrusted-forest-plan-v1",
        "status": "development-non-release",
        "claim": "untrusted plan only; no theorem or release evidence",
        "logs": [_identity(path) for path in paths],
        "summary": {
            "roots": len(leaves),
            "direct": sum(leaf.depth == 0 for leaf in leaves),
            "depth1": sum(leaf.depth == 1 for leaf in leaves),
            "depth2": sum(leaf.depth == 2 for leaf in leaves),
            "unresolved": sum(leaf.depth is None for leaf in leaves),
            "final_cells": sum(leaf.final_cells for leaf in leaves),
        },
        "leaves": [asdict(leaf) for leaf in leaves],
    }
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", type=Path, action="append", required=True)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--stop", type=int, required=True)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-ml", type=Path)
    parser.add_argument("--ml-name", default="candle_action296_generated")
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()
    leaves = read_logs(args.log, require_complete=not args.allow_partial)
    validate_range(leaves, args.start, args.stop)
    args.output_json.write_text(render_json(leaves, args.log), encoding="utf-8")
    if args.output_ml is not None:
        args.output_ml.write_text(
            render_ml(leaves, args.ml_name), encoding="utf-8"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
