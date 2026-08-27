#!/usr/bin/env python3
"""Create one strict-decoding rejection case for every supported PFT command."""

from __future__ import annotations

import argparse
from pathlib import Path

from inspect_opcodes import OPCODE_NAMES, inspect_with_positions


NON_CANONICAL_ZERO = b"\x80\x00"


def safe_name(name: str) -> str:
    return name.lower().replace("_", "-")


def mutate(output_dir: Path, traces: list[Path]) -> None:
    output_dir.mkdir(parents=True, exist_ok=False)
    occurrences: dict[str, tuple[Path, int]] = {}
    for trace in traces:
        _, positions = inspect_with_positions(trace)
        for name, position in positions.items():
            occurrences.setdefault(name, (trace, position))

    missing = sorted(set(OPCODE_NAMES.values()) - set(occurrences))
    if missing:
        raise ValueError(f"cannot mutate absent opcodes: {', '.join(missing)}")

    opcodes_by_name = {name: opcode for opcode, name in OPCODE_NAMES.items()}
    for name in sorted(occurrences):
        trace, position = occurrences[name]
        data = trace.read_bytes()
        opcode = opcodes_by_name[name]
        if data[position] != opcode:
            raise AssertionError(f"opcode position changed for {name}")
        mutated = data[: position + 1] + NON_CANONICAL_ZERO + data[position + 1 :]
        output = output_dir / f"bad-{opcode:02x}-{safe_name(name)}.pft.bin"
        output.write_bytes(mutated)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("trace", nargs="+", type=Path)
    args = parser.parse_args()
    mutate(args.output_dir, args.trace)


if __name__ == "__main__":
    main()
