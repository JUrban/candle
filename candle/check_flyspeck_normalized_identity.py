#!/usr/bin/env python3
"""Reject executable physical-identity operators in normalized source files."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

import flyspeck_manifest
import flyspeck_normalize


PHYSICAL_OPERATOR = re.compile(r"!=(?!=)|(?<![=])==(?!=|>)")


def executable_physical_operators(source: str) -> list[tuple[int, str]]:
    masked = flyspeck_manifest._code_mask(
        flyspeck_manifest.strip_ocaml_comments(source)
    )
    return [
        (masked.count("\n", 0, match.start()) + 1, match.group(0))
        for match in PHYSICAL_OPERATOR.finditer(masked)
    ]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument(
        "--contract", type=Path,
        default=Path(__file__).with_name(flyspeck_normalize.CONTRACT_NAME),
    )
    arguments = parser.parse_args()
    _, outputs = flyspeck_normalize.evaluate_contract(
        arguments.contract.resolve(), arguments.flyspeck_root.resolve(),
    )
    failures: list[str] = []
    for entry, normalized in outputs:
        findings = executable_physical_operators(normalized.decode("utf-8"))
        if findings:
            failures.append(f"{entry['path']}: {findings}")
    if failures:
        raise SystemExit(
            "normalized executable physical-identity operators remain: "
            + "; ".join(failures)
        )
    print(
        f"normalized identity scan ok: {len(outputs)} files, "
        "0 executable physical operators"
    )


if __name__ == "__main__":
    main()
