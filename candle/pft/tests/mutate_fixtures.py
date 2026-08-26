#!/usr/bin/env python3
"""Create deterministic malformed PFT inputs from the HOL4 golden fixture."""

from __future__ import annotations

import argparse
from pathlib import Path


def replace_once(data: bytes, old: bytes, new: bytes, label: str) -> bytes:
    if data.count(old) != 1:
        raise ValueError(f"{label}: expected one {old!r}, found {data.count(old)}")
    return data.replace(old, new, 1)


def write(output_dir: Path, name: str, data: bytes) -> None:
    (output_dir / f"{name}.pft.bin").write_bytes(data)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("fixture", type=Path)
    parser.add_argument("output_dir", type=Path)
    args = parser.parse_args()

    source = args.fixture.read_bytes()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if not source.startswith(b"PFT\0\x050.1.0\x06candle"):
        raise ValueError("unexpected golden fixture header")
    if source[-6:] != b"\xff\x03\x04\x03\x04\x00":
        raise ValueError("unexpected golden fixture footer")

    changed = bytearray(source)
    changed[0] = 0
    write(args.output_dir, "bad-magic", bytes(changed))

    changed = bytearray(source)
    changed[5] = ord("9")
    write(args.output_dir, "bad-version", bytes(changed))

    changed = bytearray(source)
    changed[11] = ord("x")
    write(args.output_dir, "bad-ruleset", bytes(changed))

    write(
        args.output_dir,
        "unknown-opcode",
        replace_once(source, b"\x10\x00\x01", b"\x0a\x00\x01", "REFL"),
    )
    write(
        args.output_dir,
        "dead-input-id",
        replace_once(source, b"\x10\x00\x01", b"\x10\x00\x04", "REFL"),
    )
    write(
        args.output_dir,
        "live-result-id",
        replace_once(source, b"\x20\x01\x00", b"\x20\x00\x00", "SYM"),
    )
    write(
        args.output_dir,
        "noncanonical-varint",
        replace_once(source, b"\x10\x00\x01", b"\x10\x80\x00\x01", "REFL"),
    )
    write(
        args.output_dir,
        "invalid-utf8",
        replace_once(source, b"\x03\x01\x01p\x00", b"\x03\x01\x01\x80\x00", "VAR"),
    )

    changed = bytearray(source)
    changed[-6] = 0xFE
    write(args.output_dir, "bad-footer-opcode", bytes(changed))

    changed = bytearray(source)
    changed[-5] = 2
    write(args.output_dir, "undersized-footer-limit", bytes(changed))

    write(args.output_dir, "trailing-byte", source + b"\0")
    write(args.output_dir, "truncated", source[:-1])


if __name__ == "__main__":
    main()
