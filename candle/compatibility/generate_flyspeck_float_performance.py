#!/usr/bin/env python3
"""Generate exact, provenance-bound Flyspeck float performance inputs.

This generator has two deliberately separate products:

* the complete decimal-literal spelling histogram from the pinned
  ``break_case_log.hl`` source; and
* matched call-time and hoisted-constant loop sources for the three decimal
  spellings whose conversion placement is performance-relevant.

The products are performance inputs only.  They do not check theorems and are
never S2 or S3 evidence.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
from typing import Any


SOURCE_KEY = "flyspeck:text_formalization/nonlinear/break_case_log.hl"
SOURCE_PATH = Path("text_formalization/nonlinear/break_case_log.hl")
EXPECTED_FLYSPECK_COMMIT = "1ce0353008eba83d3c76ae9a25c3c242e4802d53"
EXPECTED_MANIFEST_SHA256 = (
    "1521484e31ae03404d5395dfa4c3496e6cc9f3f213f2017422709fc86b7838d1"
)
EXPECTED_SOURCE = {
    "bytes": 827309,
    "md5": "0d51ddd36c8501cdf881eef684752195",
    "sha256": "2b3c74156a5ee9a6b3b5b6905ff28a7fb21e7c50052ad37887b90b9ed3d5e499",
}
EXPECTED_FACET_COUNT = 15462
EXPECTED_LEAF_COUNT = 7479
EXPECTED_ADD_CASE_COUNT = 463
EXPECTED_HALF_SPELLING_COUNT = 11640
EXPECTED_UNIQUE_FLOAT_SPELLINGS = 1705
EXPECTED_HISTOGRAM_SHA256 = (
    "242086f2834fbcb3028d411b40bb37a7105be13ff78b6c1d487805ac7ee7edda"
)
DEFAULT_ITERATIONS = 10000
CLAIM = "performance input only; not semantic, S2, or S3 evidence"

FLOAT_TOKEN = re.compile(
    r"(?<![A-Za-z0-9_'])(?:[0-9][0-9_]*\.[0-9_]+"
    r"(?:[eE][+-]?[0-9][0-9_]*)?)(?![A-Za-z0-9_'])"
)

FLOAT_WORDS = {
    "10000.0": 4666723172467343360,
    "1.0": 4607182418800017408,
    "1.0e-10": 4457293557087583675,
}


class InputError(ValueError):
    """The requested performance input is not the pinned corpus."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InputError(message)


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def file_record(path: Path) -> dict[str, Any]:
    value = path.read_bytes()
    return {"bytes": len(value), "sha256": sha256_bytes(value)}


def _fixed_git(root: Path, *arguments: str) -> str:
    return subprocess.run(
        ["/usr/bin/git", "-C", str(root), *arguments], check=True,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
    ).stdout.strip()


def _code_only(source: str) -> str:
    """Mask nested comments and strings while preserving source positions."""

    result = list(source)
    index = 0
    comment_depth = 0
    in_string = False
    escaped = False
    while index < len(source):
        pair = source[index:index + 2]
        character = source[index]
        if comment_depth:
            if pair == "(*":
                result[index:index + 2] = "  "
                comment_depth += 1
                index += 2
                continue
            if pair == "*)":
                result[index:index + 2] = "  "
                comment_depth -= 1
                index += 2
                continue
            if character != "\n":
                result[index] = " "
            index += 1
            continue
        if in_string:
            if character != "\n":
                result[index] = " "
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue
        if pair == "(*":
            result[index:index + 2] = "  "
            comment_depth = 1
            index += 2
            continue
        if character == '"':
            result[index] = " "
            in_string = True
        index += 1
    require(comment_depth == 0, "unterminated OCaml comment in pinned source")
    require(not in_string, "unterminated OCaml string in pinned source")
    return "".join(result)


def histogram_record(source: str) -> dict[str, Any]:
    code = _code_only(source)
    spellings = FLOAT_TOKEN.findall(code)
    histogram = dict(sorted(Counter(spellings).items()))
    encoded_histogram = json.dumps(
        histogram, sort_keys=True, separators=(",", ":"),
    ).encode("utf-8")
    record = {
        "decimal_term_count": len(spellings),
        "iarg_facet_count": len(re.findall(r"\bIarg_facet\b", code)),
        "iarg_leaf_count": len(re.findall(r"\bIarg_leaf\b", code)),
        "add_case_count": len(re.findall(r"(?m)^\s*add_case\s*\(", code)),
        "unique_spelling_count": len(histogram),
        "zero_point_5000_count": histogram.get("0.5000", 0),
        "canonical_histogram_sha256": sha256_bytes(encoded_histogram),
        "histogram": histogram,
    }
    require(record["decimal_term_count"] == EXPECTED_FACET_COUNT,
            "break_case_log decimal-term count drift")
    require(record["iarg_facet_count"] == EXPECTED_FACET_COUNT,
            "break_case_log Iarg_facet count drift")
    require(record["decimal_term_count"] == record["iarg_facet_count"],
            "decimal terms no longer correspond one-for-one with Iarg_facet")
    require(record["iarg_leaf_count"] == EXPECTED_LEAF_COUNT,
            "break_case_log Iarg_leaf count drift")
    require(record["add_case_count"] == EXPECTED_ADD_CASE_COUNT,
            "break_case_log add_case count drift")
    require(record["zero_point_5000_count"] == EXPECTED_HALF_SPELLING_COUNT,
            "break_case_log 0.5000 spelling count drift")
    require(record["unique_spelling_count"] == EXPECTED_UNIQUE_FLOAT_SPELLINGS,
            "break_case_log unique float spelling count drift")
    require(record["canonical_histogram_sha256"] == EXPECTED_HISTOGRAM_SHA256,
            "break_case_log full float histogram drift")
    return record


def validate_inputs(candle_root: Path, flyspeck_root: Path) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    manifest_path = candle_root / "candle/flyspeck_manifest.json"
    require(manifest_path.is_file() and not manifest_path.is_symlink(),
            f"missing ordinary Flyspeck manifest: {manifest_path}")
    manifest_bytes = manifest_path.read_bytes()
    manifest_sha256 = sha256_bytes(manifest_bytes)
    require(manifest_sha256 == EXPECTED_MANIFEST_SHA256,
            "Flyspeck manifest sha256 drift")
    manifest = json.loads(manifest_bytes)
    require(manifest.get("schema") == 1, "unsupported Flyspeck manifest schema")
    pinned_commit = manifest.get("repositories", {}).get("flyspeck", {}).get("commit")
    require(pinned_commit == EXPECTED_FLYSPECK_COMMIT,
            "manifest Flyspeck commit differs from the performance contract")
    node = manifest.get("source_nodes", {}).get(SOURCE_KEY)
    require(isinstance(node, dict), "break_case_log is absent from source graph")
    require(node.get("repository") == "flyspeck" and
            node.get("path") == SOURCE_PATH.as_posix(),
            "break_case_log source-node identity drift")
    for field, expected in EXPECTED_SOURCE.items():
        require(node.get(field) == expected,
                f"break_case_log manifest {field} drift")

    require(_fixed_git(flyspeck_root, "rev-parse", "HEAD") == pinned_commit,
            "Flyspeck worktree is not at the manifest pin")
    require(not _fixed_git(
        flyspeck_root, "status", "--porcelain", "--untracked-files=all"),
        "Flyspeck worktree is not clean")
    source_path = (flyspeck_root / SOURCE_PATH).resolve()
    require(source_path.is_relative_to(flyspeck_root),
            "break_case_log escaped the Flyspeck root")
    require(source_path.is_file() and not source_path.is_symlink(),
            "break_case_log is not an ordinary file")
    source_bytes = source_path.read_bytes()
    observed_source = {
        "bytes": len(source_bytes),
        "md5": hashlib.md5(source_bytes).hexdigest(),  # nosec: source identity
        "sha256": sha256_bytes(source_bytes),
    }
    require(observed_source == EXPECTED_SOURCE,
            "break_case_log bytes differ from the manifest node")
    return {
        "manifest": {
            "path": "candle/flyspeck_manifest.json",
            "sha256": manifest_sha256,
            "source_node_count": manifest.get("source_node_count"),
            "build_sequence_count": manifest.get("build_sequence_count"),
        },
        "flyspeck": {
            "commit": pinned_commit,
            "source_key": SOURCE_KEY,
            "source_path": SOURCE_PATH.as_posix(),
            **observed_source,
        },
        "source_text": source_bytes.decode("utf-8"),
    }


def _loop_source(kind: str, iterations: int) -> str:
    require(kind in {"call_time", "hoisted"}, "unknown loop source kind")
    require(iterations > 0, "iteration count must be positive")
    prefix = f"candle_float_perf_{kind}"
    lines = [
        ("(* Generated performance workload only; this is not semantic, S2, "
         "or S3 evidence. *)"),
    ]
    if kind == "hoisted":
        for index, literal in enumerate(FLOAT_WORDS, start=1):
            lines.append(f"let {prefix}_constant_{index} = {literal};;")
        observed = [f"{prefix}_constant_{index}" for index in range(1, 4)]
    else:
        observed = list(FLOAT_WORDS)
    lines.append(f"let {prefix}_observe () =")
    for index, (expression, expected) in enumerate(
            zip(observed, FLOAT_WORDS.values())):
        suffix = " &&" if index < 2 else ";;"
        lines.append(
            "  Cake.Word64.toInt (Cake.Double.toWord "
            f"{expression}) = {expected}{suffix}")
    lines.extend([
        f"let rec {prefix}_loop remaining =",
        "  if remaining = 0 then true",
        f"  else if {prefix}_observe () then {prefix}_loop (remaining - 1)",
        "  else false;;",
        f"let {prefix}_passed = {prefix}_loop {iterations};;",
        (f"let () = if {prefix}_passed then () else failwith "
         f'"{kind} float performance observation mismatch";;'),
    ])
    return "\n".join(lines) + "\n"


def materialize(
    candle_root: Path,
    flyspeck_root: Path,
    output_dir: Path,
    iterations: int = DEFAULT_ITERATIONS,
) -> dict[str, Any]:
    require(iterations > 0, "iteration count must be positive")
    validated = validate_inputs(candle_root, flyspeck_root)
    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    output_dir = output_dir.resolve()
    require(not output_dir.is_relative_to(candle_root),
            "performance output cannot be inside the Candle source tree")
    require(not output_dir.is_relative_to(flyspeck_root),
            "performance output cannot be inside the Flyspeck source tree")
    if output_dir.exists():
        require(output_dir.is_dir(), "performance output is not a directory")
        require(not any(output_dir.iterdir()),
                "performance output directory must be empty")
    else:
        output_dir.mkdir(parents=True)

    histogram = histogram_record(validated.pop("source_text"))
    histogram_payload = {
        "schema": 1,
        "kind": "flyspeck-break-case-log-float-histogram",
        "claim": CLAIM,
        "manifest": validated["manifest"],
        "flyspeck": validated["flyspeck"],
        **histogram,
    }
    histogram_path = output_dir / "break_case_log_float_histogram.json"
    histogram_path.write_text(
        json.dumps(histogram_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    call_path = output_dir / "candle_float_call_time_loop.ml"
    call_path.write_text(_loop_source("call_time", iterations), encoding="utf-8")
    hoisted_path = output_dir / "candle_float_hoisted_loop.ml"
    hoisted_path.write_text(_loop_source("hoisted", iterations), encoding="utf-8")
    receipt = {
        "schema": 1,
        "kind": "flyspeck-float-performance-inputs",
        "claim": CLAIM,
        "manifest": validated["manifest"],
        "flyspeck": validated["flyspeck"],
        "iterations": iterations,
        "float_spellings": list(FLOAT_WORDS),
        "expected_word64_decimal": FLOAT_WORDS,
        "histogram_summary": {
            key: histogram[key] for key in (
                "decimal_term_count", "iarg_facet_count", "iarg_leaf_count",
                "add_case_count", "unique_spelling_count",
                "zero_point_5000_count", "canonical_histogram_sha256",
            )
        },
        "outputs": {
            path.name: file_record(path)
            for path in (histogram_path, call_path, hoisted_path)
        },
    }
    receipt_path = output_dir / "flyspeck_float_performance_inputs.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", type=Path, required=True)
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=DEFAULT_ITERATIONS)
    arguments = parser.parse_args()
    receipt = materialize(
        arguments.candle_root, arguments.flyspeck_root,
        arguments.output_dir, arguments.iterations,
    )
    print(json.dumps({
        "claim": receipt["claim"],
        "iterations": receipt["iterations"],
        **receipt["histogram_summary"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
