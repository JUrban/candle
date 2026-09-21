#!/usr/bin/env python3
"""Segment the generated multivariate Taylor module at closed sections.

The authenticated source places roughly 3,470 lines in one OCaml module
phrase.  This DEVELOPMENT / NON-RELEASE normalization cuts only after complete
top-level ``Sections`` regions.  Later chunks reopen the original dependency
namespaces and include the preceding chunk; the public
``Multivariate_taylor`` module includes the final chunk.
"""

from __future__ import annotations

import hashlib
from typing import Any


SOURCE_KEY = (
    "flyspeck:formal_ineqs/taylor/theory/multivariate_taylor-compiled.hl"
)
INPUT_SHA256 = (
    "939ce4620c4604d6ca1411ff78a84f9b86f5bc675e099f4b75d5d69c9b329e11"
)
NORMALIZATION_ID = "candle-nonlinear-multivariate-module-segmentation-v1"
MARKER_PREFIX = "CANDLE_NONLINEAR_MULTIVARIATE_SEGMENT"
MODULE_PREFIX = "Candle_multivariate_taylor_chunk_"

MODULE_ANCHOR = b"(* Module Multivariate_taylor*)\nmodule Multivariate_taylor = struct\n"
CLOSE_ANCHOR = b"(* Close the module *)\nend;;\n"
DEPENDENCY_OPENS = (
    b"open Ssreflect;;\n"
    b"open Ssrfun;;\n"
    b"open Ssrbool;;\n"
    b"open Ssrnat;;\n"
    b"open Taylor_interval;;\n"
    b"open Interval_arith;;\n"
)

# Each boundary follows a complete top-level section.  Nested section endings
# are deliberately not eligible boundaries.
SPLIT_ANCHORS = (
    b'Sections.end_section "Misc";;\n',
    b'Sections.end_section "Partial";;\n',
    b'Sections.end_section "PartialMonotone";;\n',
    b'Sections.end_section "Taylor";;\n',
    b'Sections.end_section "Diff2Arith";;\n',
    b'Sections.end_section "Diff2c";;\n',
    b'Sections.end_section "M_LinApprox";;\n',
    b'Sections.end_section "M_TaylorIntervalArith";;\n',
    b'Sections.end_section "PartialConvex";;\n',
)


def _identity(data: bytes) -> dict[str, Any]:
    return {
        "bytes": len(data),
        "md5": hashlib.md5(data, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _split_body(body: bytes) -> list[bytes]:
    chunks: list[bytes] = []
    offset = 0
    for anchor in SPLIT_ANCHORS:
        if body.count(anchor) != 1:
            raise ValueError(
                "multivariate segmentation anchor is absent or duplicated"
            )
        position = body.index(anchor)
        boundary = position + len(anchor)
        if boundary <= offset:
            raise ValueError("multivariate segmentation anchors are out of order")
        chunks.append(body[offset:boundary])
        offset = boundary
    chunks.append(body[offset:])
    if any(not chunk.strip() for chunk in chunks):
        raise ValueError("multivariate segmentation produced an empty chunk")
    if b"".join(chunks) != body:
        raise ValueError("multivariate segmentation body reconstruction failed")
    return chunks


def _module_name(index: int) -> str:
    return f"{MODULE_PREFIX}{index:03d}"


def _marker(index: int, event: str) -> bytes:
    return (
        f'let _ = print_endline "{MARKER_PREFIX} index={index} '
        f'event={event}";;\n'
    ).encode("ascii")


def _render_chunk(index: int, chunk: bytes) -> bytes:
    name = _module_name(index)
    header = _marker(index, "begin") + f"module {name} = struct\n".encode(
        "ascii"
    )
    if index:
        previous = _module_name(index - 1)
        header += DEPENDENCY_OPENS + f"include {previous};;\n".encode("ascii")
    return header + chunk + b"\nend;;\n" + _marker(index, "end")


def segment_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    matches = [record for record in records if record["source_key"] == SOURCE_KEY]
    if len(matches) != 1:
        raise ValueError("multivariate segmentation source is absent or duplicated")
    record = matches[0]
    data = record["normalized_bytes"]
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise ValueError("multivariate segmentation source identity drift")
    if data.count(MODULE_ANCHOR) != 1 or data.count(CLOSE_ANCHOR) != 1:
        raise ValueError("multivariate segmentation outer anchor drift")
    prefix,remainder = data.split(MODULE_ANCHOR,1)
    body,suffix = remainder.split(CLOSE_ANCHOR,1)
    if suffix:
        raise ValueError("multivariate segmentation unexpected trailing bytes")
    if MODULE_PREFIX.encode("ascii") in body:
        raise ValueError("multivariate segmentation internal name collision")

    chunks = _split_body(body)
    rendered = b"".join(
        _render_chunk(index,chunk) for index,chunk in enumerate(chunks)
    )
    final_name = _module_name(len(chunks) - 1)
    public_wrapper = (
        b"(* Public interface preserved from the authenticated source. *)\n"
        b"module Multivariate_taylor = struct\n"
        + f"include {final_name};;\n".encode("ascii")
        + b"end;;\n"
    )
    segmented = prefix + rendered + public_wrapper
    identity = _identity(segmented)
    chunk_records = [
        {"index": index, "module": _module_name(index), **_identity(chunk)}
        for index,chunk in enumerate(chunks)
    ]
    prior = record["normalization"]
    record["normalized_bytes"] = segmented
    record["normalization"] = {
        "authority": "development-only-nonlinear-module-segmentation",
        "id": NORMALIZATION_ID,
        "semantic_rule": (
            "partition the exact authenticated multivariate Taylor module body "
            "only after fixed complete top-level Sections regions; every later "
            "internal module reopens the original dependencies and includes its "
            "exact predecessor; the public Multivariate_taylor module includes "
            "the final chunk"
        ),
        "input_normalization": prior,
        "chunk_count": len(chunks),
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
    return {
        "normalization_id": NORMALIZATION_ID,
        "source_key": SOURCE_KEY,
        "input_sha256": INPUT_SHA256,
        "marker_prefix": MARKER_PREFIX,
        "chunk_count": len(chunks),
        "chunks": chunk_records,
        "marker_count": 2 * len(chunks),
        "public_module": "Multivariate_taylor",
        "public_include": final_name,
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
