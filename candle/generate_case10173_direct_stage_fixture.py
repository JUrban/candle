#!/usr/bin/env python3
"""Generate a compact fixture from native direct-plan Taylor stages.

The resulting development-only fixture contains the center, radii, center
gradient, symmetric absolute Hessian bounds, and expected final upper endpoint
for each record.  ``.tsv`` selects the compact form consumed by the benchmark;
other suffixes retain the older closed-cval ML form for diagnostic use.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path


SCALE = 1_000_000_000_000
DIMENSION = 6


def fixed(text: str) -> int:
    value = Fraction(text)
    scaled = value * SCALE
    if scaled.denominator != 1:
        raise ValueError(f"non-fixed-grid value: {text}")
    return scaled.numerator


def signed(value: int) -> str:
    if value >= 0:
        return f"Cexp_pair (Cexp_num {value}) (Cexp_num 0)"
    return f"Cexp_pair (Cexp_num 0) (Cexp_num {-value})"


def interval(lower: int, upper: int) -> str:
    if lower > upper:
        raise ValueError("empty interval")
    return f"Cexp_pair ({signed(lower)}) ({signed(upper)})"


def cval_list(items: list[str]) -> str:
    result = "Cexp_num 0"
    for item in reversed(items):
        result = f"Cexp_pair ({item}) ({result})"
    return result


def parse_fields(line: str) -> dict[str, str]:
    prefix = "CANDLE_NL_NATIVE_FIXED_SCALE_STAGE "
    if not line.startswith(prefix):
        raise ValueError("unexpected native stage record")
    fields: dict[str, str] = {}
    for item in line[len(prefix) :].strip().split():
        key, value = item.split("=", 1)
        fields[key] = value
    return fields


def parse_interval(text: str) -> tuple[int, int]:
    lower, upper = text.split(":", 1)
    return fixed(lower), fixed(upper)


def record(fields: dict[str, str], expected_index: int) -> str:
    if int(fields["index"]) != expected_index:
        raise ValueError("non-consecutive native stage index")
    center = interval(*parse_interval(fields["center"]))
    radii_values = [fixed(item) for item in fields["widths"].split(",")]
    gradients = [
        interval(*parse_interval(item))
        for item in fields["center_gradient"].split(",")
    ]
    upper_triangle = [fixed(item) for item in fields["hessian_abs"].split(",")]
    if len(radii_values) != DIMENSION or len(gradients) != DIMENSION:
        raise ValueError("dimension drift")
    if len(upper_triangle) != DIMENSION * (DIMENSION + 1) // 2:
        raise ValueError("symmetric Hessian shape drift")

    absolute: dict[tuple[int, int], int] = {}
    cursor = 0
    for row in range(DIMENSION):
        for column in range(row, DIMENSION):
            value = upper_triangle[cursor]
            cursor += 1
            if value < 0:
                raise ValueError("negative absolute Hessian bound")
            absolute[row, column] = value
            absolute[column, row] = value
    hessian = cval_list(
        [
            cval_list(
                [interval(-absolute[row, column], absolute[row, column])
                 for column in range(DIMENSION)]
            )
            for row in range(DIMENSION)
        ]
    )
    radii = cval_list([signed(value) for value in radii_values])
    gradient = cval_list(gradients)
    expected = signed(fixed(fields["upper"]))
    return cval_list([center, radii, gradient, hessian, expected])


def compact_record(fields: dict[str, str], expected_index: int) -> str:
    if int(fields["index"]) != expected_index:
        raise ValueError("non-consecutive native stage index")
    _, center_upper = parse_interval(fields["center"])
    radii = [fixed(item) for item in fields["widths"].split(",")]
    gradients = [
        max(abs(lower), abs(upper))
        for lower, upper in
        (parse_interval(item) for item in fields["center_gradient"].split(","))
    ]
    hessian = [fixed(item) for item in fields["hessian_abs"].split(",")]
    expected = fixed(fields["upper"])
    if len(radii) != DIMENSION or len(gradients) != DIMENSION:
        raise ValueError("dimension drift")
    if len(hessian) != DIMENSION * (DIMENSION + 1) // 2:
        raise ValueError("symmetric Hessian shape drift")
    if any(value < 0 for value in radii + gradients + hessian):
        raise ValueError("negative compact absolute bound")
    return " ".join(
        str(value)
        for value in
        [expected_index, center_upper, *radii, *gradients, *hessian, expected]
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    lines = [line for line in args.input.read_text().splitlines() if line]
    if len(lines) != 128:
        raise ValueError(f"expected 128 stage records, found {len(lines)}")
    parsed = [parse_fields(line) for line in lines]
    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.output.suffix == ".tsv":
        args.output.write_text(
            "\n".join(
                compact_record(fields, index)
                for index, fields in enumerate(parsed)
            ) + "\n"
        )
    else:
        records = [record(fields, index) for index, fields in enumerate(parsed)]
        payload = cval_list(records)
        args.output.write_text(
            "(* Generated DEVELOPMENT / NON-RELEASE case-10173 stage fixture. *)\n"
            "let candle_case10173_direct_stage_prefix128 =\n"
            f" `{payload}`;;\n"
        )


if __name__ == "__main__":
    main()
