#!/usr/bin/env python3
"""Append a positive COMPUTE transaction to an exported compute basis."""

from __future__ import annotations

import argparse
import os
import tempfile
from pathlib import Path


EQUATION_NAMES = [f"candle$COMPUTE_EQ_{index:02d}" for index in range(62)]


def encode_varint(value: int) -> bytes:
    if value < 0:
        raise ValueError("negative varint")
    result = bytearray()
    while value >= 0x80:
        result.append((value & 0x7F) | 0x80)
        value >>= 7
    result.append(value)
    return bytes(result)


def encode_string(value: str) -> bytes:
    encoded = value.encode("utf-8")
    return encode_varint(len(encoded)) + encoded


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
            if byte_count and not byte & 0x80 and payload == 0:
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

    def string(self) -> str:
        return self.raw(self.varint()).decode("utf-8")

    def varints(self, count: int) -> None:
        for _ in range(count):
            self.varint()


def parse_basis(data: bytes) -> tuple[int, tuple[int, int, int]]:
    decoder = Decoder(data)
    if decoder.raw(4) != b"PFT\0":
        raise ValueError("bad PFT magic")
    if decoder.string() != "0.1.0" or decoder.string() != "candle":
        raise ValueError("unsupported PFT header")

    saves: list[str] = []
    while decoder.position < len(data):
        command_start = decoder.position
        opcode = decoder.byte()
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
            saves.append(decoder.string()); decoder.varint()
        elif opcode == 0x51:
            decoder.varint(); decoder.string()
        elif opcode in (0xE0, 0xE1, 0xE2):
            decoder.varint()
        elif opcode == 0xEF:
            decoder.varint(); decoder.varints(decoder.varint()); decoder.varint()
        elif opcode in (0xF0, 0xF1, 0xF2):
            decoder.varints(2)
        elif opcode == 0xFF:
            limits = (decoder.varint(), decoder.varint(), decoder.varint())
            encoded_length = int.from_bytes(decoder.raw(2), "little")
            if encoded_length != decoder.position - command_start - 2:
                raise ValueError("incorrect footer length")
            if decoder.position != len(data):
                raise ValueError("trailing bytes after footer")
            if saves != EQUATION_NAMES:
                raise ValueError("basis does not save the 62 equations in order")
            return command_start, limits
        else:
            raise ValueError(f"unknown opcode 0x{opcode:02x}")
    raise ValueError("missing footer")


class Encoder:
    def __init__(self, prefix: bytes) -> None:
        self.data = bytearray(prefix)

    def command(self, opcode: int, *fields: bytes) -> None:
        self.data.append(opcode)
        for field in fields:
            self.data.extend(field)

    def tyop(self, identifier: int, name: str, arguments: list[int]) -> None:
        self.command(
            0x02,
            encode_varint(identifier),
            encode_string(name),
            encode_varint(len(arguments)),
            *(encode_varint(argument) for argument in arguments),
        )

    def const(self, identifier: int, name: str, type_id: int) -> None:
        self.command(
            0x04,
            encode_varint(identifier),
            encode_string(name),
            encode_varint(type_id),
        )

    def comb(self, identifier: int, rator_id: int, rand_id: int) -> None:
        self.command(
            0x05,
            encode_varint(identifier),
            encode_varint(rator_id),
            encode_varint(rand_id),
        )


def generate(basis: Path, output: Path) -> None:
    if basis.resolve() == output.resolve():
        raise ValueError("basis and output must be different files")
    data = basis.read_bytes()
    footer_start, (type_limit, term_limit, theorem_limit) = parse_basis(data)
    encoder = Encoder(data[:footer_start])

    loaded_equations = list(range(theorem_limit, theorem_limit + 62))
    for theorem_id, name in zip(loaded_equations, EQUATION_NAMES, strict=True):
        encoder.command(0x51, encode_varint(theorem_id), encode_string(name))
    encoder.command(
        0x40,
        encode_varint(len(loaded_equations)),
        *(encode_varint(theorem_id) for theorem_id in loaded_equations),
    )

    num_type = type_limit
    cval_type = type_limit + 1
    bool_type = type_limit + 2
    num_to_num_type = type_limit + 3
    num_to_cval_type = type_limit + 4
    cval_to_bool_type = type_limit + 5
    cval_equality_type = type_limit + 6
    encoder.tyop(num_type, "num", [])
    encoder.tyop(cval_type, "cval", [])
    encoder.tyop(bool_type, "bool", [])
    encoder.tyop(num_to_num_type, "fun", [num_type, num_type])
    encoder.tyop(num_to_cval_type, "fun", [num_type, cval_type])
    encoder.tyop(cval_to_bool_type, "fun", [cval_type, bool_type])
    encoder.tyop(cval_equality_type, "fun", [cval_type, cval_to_bool_type])

    zero_constant = term_limit
    numeral_constant = term_limit + 1
    numeral_zero = term_limit + 2
    cexp_num_constant = term_limit + 3
    cexp_zero = term_limit + 4
    equality_constant = term_limit + 5
    equality_left = term_limit + 6
    equality = term_limit + 7
    encoder.const(zero_constant, "_0", num_type)
    encoder.const(numeral_constant, "NUMERAL", num_to_num_type)
    encoder.comb(numeral_zero, numeral_constant, zero_constant)
    encoder.const(cexp_num_constant, "Cexp_num", num_to_cval_type)
    encoder.comb(cexp_zero, cexp_num_constant, numeral_zero)
    encoder.const(equality_constant, "=", cval_equality_type)
    encoder.comb(equality_left, equality_constant, cexp_zero)
    encoder.comb(equality, equality_left, cexp_zero)

    result_theorem = theorem_limit + 62
    encoder.command(
        0x41,
        encode_varint(result_theorem),
        encode_varint(cexp_zero),
        encode_varint(0),
    )
    encoder.command(
        0xEF,
        encode_varint(result_theorem),
        encode_varint(0),
        encode_varint(equality),
    )
    encoder.command(
        0x50,
        encode_string("candle$COMPUTE_ZERO"),
        encode_varint(result_theorem),
    )

    new_limits = (type_limit + 7, term_limit + 8, theorem_limit + 63)
    footer = b"\xff" + b"".join(encode_varint(value) for value in new_limits)
    encoder.data.extend(footer)
    encoder.data.extend(len(footer).to_bytes(2, "little"))

    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=output.name + ".", dir=output.parent
    )
    try:
        with os.fdopen(descriptor, "wb") as temporary:
            temporary.write(encoder.data)
        os.replace(temporary_name, output)
    except BaseException:
        try:
            os.unlink(temporary_name)
        except FileNotFoundError:
            pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("basis", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    generate(args.basis, args.output)


if __name__ == "__main__":
    main()
