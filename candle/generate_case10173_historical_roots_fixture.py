#!/usr/bin/env python3
"""Extract development-only center/box historical-dihedral root intervals."""

from __future__ import annotations

import argparse
from pathlib import Path


PREFIX = "CANDLE_NL_NATIVE_HISTORICAL_DIHEDRAL_KERNEL "
ROOT_FIELDS = (
    "center_root_delta",
    "center_root_four_x0",
    "box_root_delta",
    "box_root_four_x0",
)


def parse(line: str) -> dict[str, str]:
    if not line.startswith(PREFIX):
        raise ValueError("unexpected historical-dihedral trace record")
    result: dict[str, str] = {}
    for item in line[len(PREFIX) :].strip().split():
        key, value = item.split("=", 1)
        result[key] = value
    return result


def endpoints(text: str) -> tuple[int, int]:
    lower, upper = text.split(":", 1)
    return int(lower), int(upper)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--count", type=int, default=None)
    args = parser.parse_args()

    source = [line for line in args.input.read_text().splitlines() if line]
    if args.count is not None:
        source = source[: args.count]
    # These intervals are untrusted benchmark inputs.  The experimental ML
    # splice seals them as data but does not yet validate their sqrt contracts;
    # they therefore must not be used as release evidence.
    rows: list[str] = []
    for expected_index, line in enumerate(source):
        record = parse(line)
        if int(record["index"]) != expected_index:
            raise ValueError("non-consecutive historical-dihedral trace")
        values = [expected_index]
        for field in ROOT_FIELDS:
            values.extend(endpoints(record[field]))
        if len(values) != 9:
            raise AssertionError("historical roots fixture width drift")
        rows.append(" ".join(str(value) for value in values))
    if not rows:
        raise ValueError("empty historical-dihedral trace")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join(rows) + "\n")


if __name__ == "__main__":
    main()
