#!/usr/bin/env python3
"""Flatten native historical-dihedral second-order trace records.

The output is DEVELOPMENT / NON-RELEASE fixture data.  Each row contains an
index, six fixed box intervals, two fixed square-root certificates, and the
native value, gradient, and upper-triangular Hessian.  The reflected program
recomputes every other derivative and enclosure result.
"""

from __future__ import annotations

import argparse
from pathlib import Path


PREFIX = "CANDLE_NL_NATIVE_HISTORICAL_DIHEDRAL_KERNEL "


def fields(line: str) -> dict[str, str]:
    if not line.startswith(PREFIX):
        raise ValueError("unexpected historical-dihedral trace record")
    result: dict[str, str] = {}
    for item in line[len(PREFIX) :].strip().split():
        key, value = item.split("=", 1)
        result[key] = value
    return result


def interval(text: str) -> list[int]:
    lower, upper = text.split(":", 1)
    return [int(lower), int(upper)]


def intervals(text: str, count: int) -> list[int]:
    values = text.split(",")
    if len(values) != count:
        raise ValueError(f"expected {count} intervals, found {len(values)}")
    return [endpoint for value in values for endpoint in interval(value)]


def row(record: dict[str, str], expected_index: int) -> str:
    if int(record["index"]) != expected_index:
        raise ValueError("non-consecutive historical-dihedral trace")
    values = [
        expected_index,
        *intervals(record["box_environment"], 6),
        *interval(record["box_root_delta"]),
        *interval(record["box_root_four_x0"]),
        *interval(record["box_value"]),
        *intervals(record["box_gradient"], 6),
        *intervals(record["hessian"], 21),
    ]
    if len(values) != 73:
        raise AssertionError("historical second-order fixture width drift")
    return " ".join(str(value) for value in values)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--count", type=int, default=None)
    args = parser.parse_args()

    source = [line for line in args.input.read_text().splitlines() if line]
    if args.count is not None:
        source = source[: args.count]
    if not source:
        raise ValueError("empty historical-dihedral trace")
    parsed = [fields(line) for line in source]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        "\n".join(row(record, index) for index, record in enumerate(parsed))
        + "\n"
    )


if __name__ == "__main__":
    main()
