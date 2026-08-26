#!/usr/bin/env python3
"""Report PFT command coverage without constructing logical objects."""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


OPCODE_NAMES = {
    0x01: "TYVAR",
    0x02: "TYOP",
    0x03: "VAR",
    0x04: "CONST",
    0x05: "COMB",
    0x06: "ABS",
    0x07: "NEW_CONST",
    0x08: "NEW_TYPE",
    0x09: "AXIOM",
    0x10: "REFL",
    0x11: "TRANS",
    0x12: "MK_COMB",
    0x13: "ABS_THM",
    0x14: "BETA",
    0x15: "ASSUME",
    0x16: "EQ_MP",
    0x17: "DEDUCT_ANTISYM",
    0x18: "INST",
    0x19: "INST_TYPE",
    0x20: "SYM",
    0x21: "PROVE_HYP",
    0x30: "NEW_SPECIFICATION",
    0x31: "NEW_TYPE_DEFINITION",
    0x40: "COMPUTE_INIT",
    0x41: "COMPUTE",
    0x50: "SAVE",
    0x51: "LOAD",
    0xE0: "DEL_TYPE",
    0xE1: "DEL_TERM",
    0xE2: "DEL_THEOREM",
    0xEF: "EXPECT",
    0xF0: "DEL_TYPE_RANGE",
    0xF1: "DEL_TERM_RANGE",
    0xF2: "DEL_THEOREM_RANGE",
    0xFF: "FOOTER",
}


class Decoder:
    def __init__(self, data: bytes) -> None:
        self.data = data
        self.position = 0

    def byte(self) -> int:
        if self.position >= len(self.data):
            raise ValueError("unexpected EOF")
        result = self.data[self.position]
        self.position += 1
        return result

    def varint(self) -> int:
        result = 0
        shift = 0
        for byte_count in range(9):
            byte = self.byte()
            payload = byte & 0x7F
            if byte_count and not (byte & 0x80) and payload == 0:
                raise ValueError("non-canonical varint")
            result |= payload << shift
            if not byte & 0x80:
                return result
            shift += 7
        raise ValueError("overlong varint")

    def raw(self, length: int) -> bytes:
        end = self.position + length
        if end > len(self.data):
            raise ValueError("truncated field")
        result = self.data[self.position:end]
        self.position = end
        return result

    def string(self) -> bytes:
        return self.raw(self.varint())

    def varints(self, count: int) -> None:
        for _ in range(count):
            self.varint()


def inspect(path: Path) -> dict[str, object]:
    decoder = Decoder(path.read_bytes())
    if decoder.raw(4) != b"PFT\0":
        raise ValueError("bad PFT magic")
    version = decoder.string().decode("utf-8")
    ruleset = decoder.string().decode("utf-8")
    counts: Counter[str] = Counter()
    footer_length: int | None = None

    while decoder.position < len(decoder.data):
        opcode = decoder.byte()
        try:
            name = OPCODE_NAMES[opcode]
        except KeyError as error:
            raise ValueError(f"unknown opcode 0x{opcode:02x}") from error
        counts[name] += 1

        if opcode == 0x01:
            decoder.varint(); decoder.string()
        elif opcode == 0x02:
            decoder.varint(); decoder.string(); decoder.varints(decoder.varint())
        elif opcode in (0x03, 0x04):
            decoder.varint(); decoder.string(); decoder.varint()
        elif opcode in (0x05, 0x06, 0x11, 0x12, 0x13, 0x16, 0x17, 0x21):
            decoder.varints(3)
        elif opcode in (0x07, 0x08):
            decoder.string(); decoder.varint()
        elif opcode == 0x09:
            decoder.varints(2); decoder.string()
        elif opcode in (0x10, 0x14, 0x15, 0x20):
            decoder.varints(2)
        elif opcode in (0x18, 0x19):
            decoder.varints(2); decoder.varints(2 * decoder.varint())
        elif opcode == 0x30:
            decoder.varints(2)
            for _ in range(decoder.varint()):
                decoder.string()
        elif opcode == 0x31:
            decoder.varints(2)
            decoder.string(); decoder.string(); decoder.string()
        elif opcode == 0x40:
            decoder.varints(decoder.varint())
        elif opcode == 0x41:
            decoder.varints(2); decoder.varints(decoder.varint())
        elif opcode == 0x50:
            decoder.string(); decoder.varint()
        elif opcode == 0x51:
            decoder.varint(); decoder.string()
        elif opcode in (0xE0, 0xE1, 0xE2):
            decoder.varint()
        elif opcode == 0xEF:
            decoder.varint(); decoder.varints(decoder.varint()); decoder.varint()
        elif opcode in (0xF0, 0xF1, 0xF2):
            decoder.varints(2)
        elif opcode == 0xFF:
            decoder.varints(3)
            footer_length = int.from_bytes(decoder.raw(2), "little")
            if decoder.position != len(decoder.data):
                raise ValueError("trailing bytes after footer")
            break
        else:  # pragma: no cover - exhaustive guard for future protocol edits
            raise AssertionError(name)

    if footer_length is None:
        raise ValueError("missing footer")

    return {
        "path": str(path),
        "version": version,
        "ruleset": ruleset,
        "commands": sum(counts.values()) + 1,
        "opcodes": dict(sorted(counts.items())),
        "footer_encoded_length": footer_length,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("trace", nargs="+", type=Path)
    args = parser.parse_args()
    print(json.dumps([inspect(path) for path in args.trace], indent=2))


if __name__ == "__main__":
    main()
