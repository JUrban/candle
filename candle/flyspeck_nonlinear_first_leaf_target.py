#!/usr/bin/env python3
"""Pin the first substantial Flyspeck nonlinear checker target.

The retained Azure result is an oracle for target identity and the historical
native result only.  It is not imported as Candle proof evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CLOSURE = Path("candle/flyspeck_nonlinear_verifier_closure.json")
OUTPUT = Path("candle/flyspeck_nonlinear_first_leaf_target.json")
CASE_ID = "prep-4680581274 delta issue-cayleyR"
GLOBAL_CASE = 7853
LOCAL_CASE = 0
AZURE_STDOUT = Path("azure/results/urban/out/1/7850/2/7899/stdout")
BREAK_LOG = Path("text_formalization/nonlinear/break_case_log.hl")
PREP = Path("text_formalization/nonlinear/prep.hl")
MAIN_VERIFIER = Path("azure/main_verifier.hl")
PROVE_BY_REFINEMENT = Path(
    "text_formalization/general/prove_by_refinement.hl"
)
COMPILED_DEFINITIONS = Path("azure/flyspeck-nat/definitions.hl")
COMPILED_BREAK_CASE = Path("azure/flyspeck-nat/break_case.hl")


def _hash(path: Path, algorithm: str = "sha256") -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def _identity(root: Path, relative: Path) -> dict[str, Any]:
    path = root / relative
    if not path.is_file() or path.is_symlink():
        raise ValueError(f"target evidence is not an ordinary file: {relative}")
    return {
        "logical_relative_path": relative.as_posix(),
        "bytes": path.stat().st_size,
        "sha256": _hash(path),
    }


def _git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def _fraction_record(value: Fraction) -> dict[str, Any]:
    denominator = value.denominator
    twos = fives = 0
    while denominator % 2 == 0:
        twos += 1
        denominator //= 2
    while denominator % 5 == 0:
        fives += 1
        denominator //= 5
    if denominator != 1:
        raise ValueError("target bound has no finite decimal representation")
    places = max(twos, fives)
    scaled = value.numerator * (10 ** places) // value.denominator
    if places == 0:
        decimal = f"{scaled}.0"
    else:
        digits = str(abs(scaled)).rjust(places + 1, "0")
        decimal = f"{digits[:-places]}.{digits[-places:]}"
        if scaled < 0:
            decimal = "-" + decimal
    return {
        "numerator": value.numerator,
        "denominator": value.denominator,
        "decimal": decimal,
    }


def _native_certificate_stats(
    stdout: str, global_case: int, label: str,
) -> dict[str, int]:
    """Extract the exact certificate-shape record paired with one theorem."""

    start = f"Verifying: {global_case}:  {label}\n"
    end = f"Theorem  {label}: |- "
    if stdout.count(start) != 1 or stdout.count(end) != 1:
        raise ValueError("retained native certificate record is ambiguous")
    section = stdout.split(start, 1)[1].split(end, 1)[0]
    if "\nVerifying: " in section:
        raise ValueError("retained native certificate record crossed a case")
    matches = re.findall(
        r"pass = ([0-9]+) \(pass_raw = ([0-9]+)\)\n"
        r"mono = ([0-9]+)\n"
        r"glue = ([0-9]+) \(glue_convex = ([0-9]+)\)\n"
        r"pass_mono = ([0-9]+)\n",
        section,
    )
    if len(matches) != 1:
        raise ValueError("retained native certificate shape is absent or ambiguous")
    leaves, raw_leaves, mono, glue, convex_glue, pass_mono = map(
        int, matches[0],
    )
    return {
        "formal_leaf_count": leaves,
        "formal_raw_leaf_count": raw_leaves,
        "formal_mono_count": mono,
        "formal_glue_count": glue,
        "formal_convex_glue_count": convex_glue,
        "formal_pass_mono_count": pass_mono,
    }


def build_target(flyspeck_root: Path) -> dict[str, Any]:
    flyspeck_root = flyspeck_root.resolve()
    closure_data = (ROOT / CLOSURE).read_bytes()
    closure = json.loads(closure_data)
    expected_head = closure["repositories"]["flyspeck"]["commit"]
    observed_head = _git_head(flyspeck_root)
    if observed_head != expected_head:
        raise ValueError("first-leaf oracle Flyspeck head differs from closure")

    stdout_path = flyspeck_root / AZURE_STDOUT
    stdout = stdout_path.read_text(encoding="utf-8")
    label = f"{GLOBAL_CASE},({CASE_ID},{LOCAL_CASE})"
    theorem_match = re.search(
        rf"Theorem  {re.escape(label)}: \|- (?P<theorem>.*?)\n"
        rf"Time  {re.escape(label)}: (?P<seconds>[0-9.]+)\n"
        rf"Hash  {re.escape(label)}: (?P<digest>[0-9a-f]{{32}})",
        stdout,
        flags=re.DOTALL,
    )
    if theorem_match is None:
        raise ValueError("retained first-leaf theorem record is absent")
    oracle_stats = _native_certificate_stats(stdout, GLOBAL_CASE, label)
    if oracle_stats != {
        "formal_leaf_count": 16,
        "formal_raw_leaf_count": 0,
        "formal_mono_count": 0,
        "formal_glue_count": 15,
        "formal_convex_glue_count": 0,
        "formal_pass_mono_count": 0,
    }:
        raise ValueError("retained first-leaf certificate shape has drifted")
    theorem = theorem_match.group("theorem")
    if (
        not theorem.startswith("ineqm [x1; x2; x3; x4; x5; x6]")
        or "frac_left 0 #0.7637" not in theorem
        or "cayleyR6u x1 x2 x3 x4 x5 x6 * -- &1 < &0" not in theorem
        or "deltaL_x4 #4.0 x1 x2 x3 x4 x5 x6 * -- &1 < &0" not in theorem
    ):
        raise ValueError("retained first-leaf theorem has unexpected interface")

    break_log = (flyspeck_root / BREAK_LOG).read_text(encoding="utf-8")
    tree_prefix = (
        f'add_case ("{CASE_ID}",\n'
        " Iarg_facet ((0,false),0.7637,800,"
    )
    if tree_prefix not in break_log:
        raise ValueError("first nonlinear tree action has drifted")

    prep = (flyspeck_root / PREP).read_text(encoding="utf-8")
    prep_anchor = f'idv= "{CASE_ID}";'
    if prep_anchor not in prep or "cayleyR6u x1 x2 x3 x4 x5 x6" not in prep:
        raise ValueError("first nonlinear inequality definition has drifted")

    verifier = (flyspeck_root / MAIN_VERIFIER).read_text(encoding="utf-8")
    if (
        "verify_flyspeck_ineq 6 ineq" not in verifier
        or "{default_params with eps = 1e-10}" not in verifier
    ):
        raise ValueError("historical verifier parameter contract has drifted")

    definitions = (flyspeck_root / COMPILED_DEFINITIONS).read_text(
        encoding="utf-8",
    )
    break_case = (flyspeck_root / COMPILED_BREAK_CASE).read_text(
        encoding="utf-8",
    )
    if (
        not definitions.startswith("open Hol_core;;\nopen Prove_by_refinement;;")
        or "let flyspeck_defs =" not in definitions
        or not break_case.startswith(
            "open Hol_core\nopen Misc\nopen Prove_by_refinement\n"
            "open Definitions\n"
        )
        or "let rec ineqm_conv =" not in break_case
    ):
        raise ValueError("first-leaf reconstruction support has drifted")

    lower = Fraction(4)
    original_upper = Fraction(2) * Fraction(126, 100)
    original_upper *= original_upper
    fraction = Fraction(7637, 10000)
    first_upper = lower * (1 - fraction) + original_upper * fraction
    if first_upper != Fraction(36218753, 6250000):
        raise AssertionError("first facet rational calculation drifted")

    bounds = [
        (Fraction(4), first_upper),
        (Fraction(4), original_upper),
        (Fraction(4), original_upper),
        (Fraction(301, 100) ** 2, Fraction(3166, 1000) ** 2),
        (Fraction(4), Fraction(4)),
        (Fraction(4), original_upper),
    ]
    return {
        "schema": 1,
        "kind": "candle-flyspeck-nonlinear-first-leaf-target",
        "status": "development-non-release",
        "claim": (
            "authenticated target/native oracle only; no Candle proof, S2, "
            "S3, qualification, promotion, or release credit"
        ),
        "flyspeck_commit": observed_head,
        "closure": {
            "path": CLOSURE.as_posix(),
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
        },
        "evidence_files": {
            "azure_stdout": _identity(flyspeck_root, AZURE_STDOUT),
            "break_case_log": _identity(flyspeck_root, BREAK_LOG),
            "prep": _identity(flyspeck_root, PREP),
            "main_verifier": _identity(flyspeck_root, MAIN_VERIFIER),
            "prove_by_refinement": _identity(
                flyspeck_root, PROVE_BY_REFINEMENT,
            ),
            "compiled_definitions": _identity(
                flyspeck_root, COMPILED_DEFINITIONS,
            ),
            "compiled_break_case": _identity(
                flyspeck_root, COMPILED_BREAK_CASE,
            ),
        },
        "target": {
            "id": CASE_ID,
            "global_case": GLOBAL_CASE,
            "local_case": LOCAL_CASE,
            "first_tree_action": {
                "kind": "Iarg_facet",
                "coordinate": 0,
                "side": "left",
                "fraction": _fraction_record(fraction),
                "archive_index": 800,
            },
            "public_bounds": [
                {
                    "variable": f"x{index}",
                    "lower": _fraction_record(lo),
                    "upper": _fraction_record(hi),
                }
                for index, (lo, hi) in enumerate(bounds, 1)
            ],
            "legacy_ineqm_text": theorem,
            "legacy_ineqm_text_sha256": hashlib.sha256(
                theorem.encode("utf-8")
            ).hexdigest(),
        },
        "native_oracle": {
            "precision": 6,
            "epsilon": "1e-10",
            "total_seconds": float(theorem_match.group("seconds")),
            "legacy_theorem_digest": theorem_match.group("digest"),
            **oracle_stats,
        },
    }


def _render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    rendered = _render(build_target(arguments.flyspeck_root))
    output = ROOT / OUTPUT
    if arguments.write:
        output.write_text(rendered, encoding="utf-8")
    elif not output.is_file() or output.read_text(encoding="utf-8") != rendered:
        raise SystemExit("stale nonlinear first-leaf target: run with --write")


if __name__ == "__main__":
    main()
