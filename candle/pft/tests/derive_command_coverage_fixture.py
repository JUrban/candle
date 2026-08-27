#!/usr/bin/env python3
"""Derive safe end-of-stream deletion coverage from the official core trace."""

from __future__ import annotations

import argparse
from pathlib import Path


EXTRA_COMMANDS = bytes(
    (
        0xE0, 0x00,  # DEL_TYPE 0
        0xE1, 0x00,  # DEL_TERM 0
        0xF2, 0x00, 0x00,  # DEL_THEOREM_RANGE 0 0
    )
)


def derive(source: Path, output: Path) -> None:
    data = source.read_bytes()
    if len(data) < 6:
        raise ValueError("core fixture is too short")
    footer_length = int.from_bytes(data[-2:], "little")
    footer_start = len(data) - footer_length - 2
    if footer_length < 4 or footer_start < 0 or data[footer_start] != 0xFF:
        raise ValueError("core fixture has an unexpected footer")
    output.write_bytes(data[:footer_start] + EXTRA_COMMANDS + data[footer_start:])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    derive(args.source, args.output)


if __name__ == "__main__":
    main()
