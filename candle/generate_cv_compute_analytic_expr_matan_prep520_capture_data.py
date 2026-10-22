#!/usr/bin/env python3
"""Materialize the exact validated prep520 capture as deterministic ML data.

DEVELOPMENT / NON-RELEASE.  The generated data is untrusted preparation.  A
proof-producing consumer must authenticate the direct source and recheck every
leaf and topology transition inside Candle.
"""

from __future__ import annotations

import hashlib
import re
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


EXPECTED_SHA256 = "e20520fdc8edcba4ff499cb5ef7e6af6b475319b7f629b887142572b588e0e08"
EXPECTED = {
    0: (401, 283, 118),
    1: (327, 321, 6),
    2: (183, 183, 0),
    3: (398, 398, 0),
}
LEAF_MARKER = "CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_LEAF "
COMPONENT_MARKER = "CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_COMPONENT_RESULT "
RESULT_MARKER = "CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_RESULT "
OK_MARKER = "CANDLE_CV_MATAN_PREP520_ALL_CAPTURE_OK"
RATIONAL = re.compile(r"^-?[0-9]+(?:/[1-9][0-9]*)?$")
TOKEN = re.compile(r"^([LR])([1-6])$")


@dataclass(frozen=True)
class Leaf:
    index: int
    branch: int
    path: tuple[tuple[str, int], ...]
    lower_text: tuple[str, ...]
    upper_text: tuple[str, ...]
    lower: tuple[Fraction, ...]
    upper: tuple[Fraction, ...]


@dataclass
class Node:
    leaf: Leaf | None = None
    axis: int | None = None
    left: "Node | None" = None
    right: "Node | None" = None


def fail(message: str) -> "None":
    raise SystemExit(f"prep520 capture materialization: {message}")


def parse_fields(text: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for item in text.split():
        if "=" in item:
            key, value = item.split("=", 1)
            fields[key] = value
    return fields


def parse_path(text: str) -> tuple[tuple[str, int], ...]:
    result = []
    for item in text.split("."):
        match = TOKEN.fullmatch(item)
        if match is None:
            fail(f"malformed path token {item!r}")
        result.append((match.group(1), int(match.group(2))))
    if not result:
        fail("empty leaf path")
    return tuple(result)


def parse_rationals(text: str) -> tuple[tuple[str, ...], tuple[Fraction, ...]]:
    items = tuple(text.split(","))
    if len(items) != 6 or any(RATIONAL.fullmatch(item) is None for item in items):
        fail(f"malformed six-dimensional rational vector {text!r}")
    return items, tuple(Fraction(item) for item in items)


def insert(root: Node, leaf: Leaf) -> None:
    node = root
    for depth, (side, axis) in enumerate(leaf.path):
        if node.leaf is not None:
            fail(f"leaf path prefixes component path at leaf {leaf.index}")
        if node.axis is None:
            node.axis = axis
        elif node.axis != axis:
            fail(f"inconsistent sibling axis at leaf {leaf.index}, depth {depth}")
        if side == "L":
            if node.left is None:
                node.left = Node()
            node = node.left
        else:
            if node.right is None:
                node.right = Node()
            node = node.right
    if node.leaf is not None or node.axis is not None or node.left is not None or node.right is not None:
        fail(f"duplicate or prefix-conflicting path at leaf {leaf.index}")
    node.leaf = leaf


def validate_tree(node: Node, component: int) -> tuple[list[Leaf], list[int], tuple[tuple[Fraction, ...], tuple[Fraction, ...]]]:
    if node.leaf is not None:
        if node.axis is not None or node.left is not None or node.right is not None:
            fail(f"component {component}: malformed leaf node")
        return [node.leaf], [0], (node.leaf.lower, node.leaf.upper)
    if node.axis is None or node.left is None or node.right is None:
        fail(f"component {component}: incomplete internal node")
    left_leaves, left_tokens, (left_lower, left_upper) = validate_tree(node.left, component)
    right_leaves, right_tokens, (right_lower, right_upper) = validate_tree(node.right, component)
    axis0 = node.axis - 1
    for coordinate in range(6):
        if coordinate == axis0:
            if left_upper[coordinate] != right_lower[coordinate]:
                fail(f"component {component}: split-face mismatch on axis {node.axis}")
        elif left_lower[coordinate] != right_lower[coordinate] or left_upper[coordinate] != right_upper[coordinate]:
            fail(f"component {component}: non-split face mismatch on axis {coordinate + 1}")
    lower = tuple(left_lower[i] if i != axis0 else left_lower[i] for i in range(6))
    upper = tuple(left_upper[i] if i != axis0 else right_upper[i] for i in range(6))
    return left_leaves + right_leaves, left_tokens + right_tokens + [node.axis], (lower, upper)


def ml_string(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def emit_vector(items: tuple[str, ...]) -> str:
    return "[" + ";".join(ml_string(item) for item in items) + "]"


def emit_component(lines: list[str], component: int, leaves: list[Leaf], tokens: list[int]) -> None:
    prefix = f"candle_matan_prep520_component{component}"
    lines.append(f"let {prefix}_leaves =")
    lines.append("  [")
    for leaf in leaves:
        lines.append(
            f"    ({leaf.branch},{emit_vector(leaf.lower_text)},{emit_vector(leaf.upper_text)});"
        )
    lines.append("  ];;")
    lines.append("")
    lines.append(f"let {prefix}_tokens =")
    for start in range(0, len(tokens), 32):
        chunk = ";".join(str(token) for token in tokens[start : start + 32])
        opener = "  [" if start == 0 else "   "
        closer = "];;" if start + 32 >= len(tokens) else ";"
        lines.append(opener + chunk + closer)
    lines.append("")


def main() -> None:
    if len(sys.argv) != 3:
        fail(f"usage: {sys.argv[0]} CAPTURE_LOG OUTPUT_ML")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2])
    payload = source.read_bytes()
    digest = hashlib.sha256(payload).hexdigest()
    if digest != EXPECTED_SHA256:
        fail(f"capture SHA-256 mismatch: expected {EXPECTED_SHA256}, got {digest}")

    leaves: dict[int, list[Leaf]] = {component: [] for component in EXPECTED}
    summaries: dict[int, tuple[int, int, int, int]] = {}
    result_count = 0
    ok_count = 0
    for line_number, raw_line in enumerate(payload.decode("utf-8").splitlines(), 1):
        if LEAF_MARKER in raw_line:
            text = raw_line[raw_line.index(LEAF_MARKER) :]
            fields = parse_fields(text)
            try:
                component = int(fields["component"])
                index = int(fields["leaf"])
                branch = int(fields["branch"])
                raw = fields["raw"]
                path = parse_path(fields["path"])
                lower_text, lower = parse_rationals(fields["lower"])
                upper_text, upper = parse_rationals(fields["upper"])
            except (KeyError, ValueError) as error:
                fail(f"malformed leaf at line {line_number}: {error}")
            if component not in EXPECTED or branch not in (0, 1) or raw != "false":
                fail(f"invalid leaf contract at line {line_number}")
            if any(lo > hi for lo, hi in zip(lower, upper)):
                fail(f"reversed interval at line {line_number}")
            leaves[component].append(Leaf(index, branch, path, lower_text, upper_text, lower, upper))
        elif COMPONENT_MARKER in raw_line:
            text = raw_line[raw_line.index(COMPONENT_MARKER) :]
            fields = parse_fields(text)
            if "source_id=prep-5202826650 a" not in text:
                fail(f"component source identity mismatch at line {line_number}")
            try:
                component = int(fields["component"])
                summary = (
                    int(fields["leaves"]),
                    int(fields["branch0"]),
                    int(fields["branch1"]),
                    int(fields["glue"]),
                )
            except (KeyError, ValueError) as error:
                fail(f"malformed component summary at line {line_number}: {error}")
            if component in summaries:
                fail(f"duplicate component summary {component}")
            summaries[component] = summary
        elif RESULT_MARKER in raw_line and COMPONENT_MARKER not in raw_line:
            if "source_id=prep-5202826650 a" not in raw_line or "components=4 leaves=1309 glue=1305" not in raw_line or "assumptions=0 axiom_growth=0" not in raw_line:
                fail(f"final result contract mismatch at line {line_number}")
            result_count += 1
        if OK_MARKER in raw_line:
            ok_count += 1

    if result_count != 1 or ok_count != 1:
        fail("missing or duplicate final capture markers")

    ordered: dict[int, tuple[list[Leaf], list[int]]] = {}
    for component, (expected_leaves, expected_branch0, expected_branch1) in EXPECTED.items():
        component_leaves = leaves[component]
        if [leaf.index for leaf in component_leaves] != list(range(expected_leaves)):
            fail(f"component {component}: leaf indexes are not exact traversal order")
        if sum(leaf.branch == 0 for leaf in component_leaves) != expected_branch0 or sum(leaf.branch == 1 for leaf in component_leaves) != expected_branch1:
            fail(f"component {component}: branch census mismatch")
        if summaries.get(component) != (expected_leaves, expected_branch0, expected_branch1, expected_leaves - 1):
            fail(f"component {component}: summary mismatch")
        root = Node()
        for leaf in component_leaves:
            insert(root, leaf)
        traversal_leaves, tokens, _ = validate_tree(root, component)
        if traversal_leaves != component_leaves:
            fail(f"component {component}: path traversal and leaf order disagree")
        if tokens.count(0) != expected_leaves or len(tokens) != 2 * expected_leaves - 1:
            fail(f"component {component}: postfix token census mismatch")
        ordered[component] = traversal_leaves, tokens

    lines = [
        "(* Generated by generate_cv_compute_analytic_expr_matan_prep520_capture_data.py.",
        "   DEVELOPMENT / NON-RELEASE: untrusted certificate preparation only. *)",
        "",
        "module Candle_cv_analytic_expr_matan_prep520_capture_data = struct",
        "",
        f"let candle_matan_prep520_capture_sha256 = {ml_string(digest)};;",
        "let candle_matan_prep520_capture_source_id = \"prep-5202826650 a\";;",
        "",
    ]
    for component in range(4):
        emit_component(lines, component, *ordered[component])
    lines.extend(
        [
            "let candle_matan_prep520_components =",
            "  [candle_matan_prep520_component0_leaves,candle_matan_prep520_component0_tokens;",
            "   candle_matan_prep520_component1_leaves,candle_matan_prep520_component1_tokens;",
            "   candle_matan_prep520_component2_leaves,candle_matan_prep520_component2_tokens;",
            "   candle_matan_prep520_component3_leaves,candle_matan_prep520_component3_tokens];;",
            "",
            "end;;",
            "",
        ]
    )
    rendered = "\n".join(lines)
    output.write_text(rendered, encoding="utf-8")
    print(
        "CANDLE_CV_MATAN_PREP520_CAPTURE_DATA_GENERATED "
        f"DEVELOPMENT_NON_RELEASE components=4 leaves=1309 tokens=2614 sha256={digest}"
    )


if __name__ == "__main__":
    main()
