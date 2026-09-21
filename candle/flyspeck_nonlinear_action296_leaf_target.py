#!/usr/bin/env python3
"""Pin the first current-source action-296 nonlinear checker target.

The retained native result identifies the target and historical performance;
it is never imported as proof evidence.  Candle must reconstruct and prove the
ordinary ``ineqm`` theorem from the authenticated current Flyspeck sources.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_first_leaf_target as common


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path("candle/flyspeck_nonlinear_action296_leaf_target.json")
CASE_ID = "prep-8657368829"
GLOBAL_CASE = 10172
LOCAL_CASE = 0
AZURE_STDOUT = Path("azure/results/urban/out/1/10150/2/10199/stdout")
FORMAL_LEAF_COUNT = 1061
FORMAL_GLUE_COUNT = 1060


def build_target(flyspeck_root: Path) -> dict[str, Any]:
    flyspeck_root = flyspeck_root.resolve()
    closure_data = (ROOT / common.CLOSURE).read_bytes()
    closure = json.loads(closure_data)
    expected_head = closure["repositories"]["flyspeck"]["commit"]
    observed_head = common._git_head(flyspeck_root)
    if observed_head != expected_head:
        raise ValueError("action-296 target Flyspeck head differs from closure")

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
        raise ValueError("retained action-296 theorem record is absent")
    oracle_stats = common._native_certificate_stats(
        stdout, GLOBAL_CASE, label,
    )
    if oracle_stats != {
        "formal_leaf_count": FORMAL_LEAF_COUNT,
        "formal_raw_leaf_count": 0,
        "formal_mono_count": 0,
        "formal_glue_count": FORMAL_GLUE_COUNT,
        "formal_convex_glue_count": 0,
        "formal_pass_mono_count": 0,
    }:
        raise ValueError("retained action-296 certificate shape has drifted")
    theorem = theorem_match.group("theorem")
    if (
        not theorem.startswith("ineqm [x1; x2; x3; x4; x5; x6]")
        or "frac_right 0 #0.5000" not in theorem
        or "dihatn_x x1 x2 x3 x4 x5 x6 * -- &1 <" not in theorem
        or "#1.277" not in theorem
    ):
        raise ValueError("retained action-296 theorem has unexpected interface")

    break_log = (flyspeck_root / common.BREAK_LOG).read_text(encoding="utf-8")
    tree = (
        f'add_case ("{CASE_ID}",\n'
        " Iarg_facet ((0,true),0.5000,716,\n"
        " Iarg_leaf 1311));;"
    )
    if tree not in break_log:
        raise ValueError("action-296 nonlinear tree has drifted")

    prep = (flyspeck_root / common.PREP).read_text(encoding="utf-8")
    if (
        f'idv= "{CASE_ID}";' not in prep
        or "dih_x x1 x2 x3 x4 x5 x6 * -- &1" not in prep
        or "sqrt_x1 x1 x2 x3 x4 x5 x6 * #0.273298" not in prep
    ):
        raise ValueError("action-296 inequality definition has drifted")

    verifier = (flyspeck_root / common.MAIN_VERIFIER).read_text(
        encoding="utf-8"
    )
    if (
        "verify_flyspeck_ineq 6 ineq" not in verifier
        or "{default_params with eps = 1e-10}" not in verifier
    ):
        raise ValueError("historical verifier parameter contract has drifted")

    definitions = (flyspeck_root / common.COMPILED_DEFINITIONS).read_text(
        encoding="utf-8"
    )
    break_case = (flyspeck_root / common.COMPILED_BREAK_CASE).read_text(
        encoding="utf-8"
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
        raise ValueError("action-296 reconstruction support has drifted")

    evidence = {
        "azure_stdout": common._identity(flyspeck_root, AZURE_STDOUT),
        "break_case_log": common._identity(flyspeck_root, common.BREAK_LOG),
        "prep": common._identity(flyspeck_root, common.PREP),
        "main_verifier": common._identity(
            flyspeck_root, common.MAIN_VERIFIER
        ),
        "prove_by_refinement": common._identity(
            flyspeck_root, common.PROVE_BY_REFINEMENT
        ),
        "compiled_definitions": common._identity(
            flyspeck_root, common.COMPILED_DEFINITIONS
        ),
        "compiled_break_case": common._identity(
            flyspeck_root, common.COMPILED_BREAK_CASE
        ),
    }
    return {
        "schema": 1,
        "kind": "candle-flyspeck-nonlinear-first-leaf-target",
        "status": "development-non-release",
        "claim": (
            "authenticated action-296 target/native oracle only; no Candle "
            "proof, S2, S3, qualification, promotion, or release credit"
        ),
        "flyspeck_commit": observed_head,
        "closure": {
            "path": common.CLOSURE.as_posix(),
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
        },
        "evidence_files": evidence,
        "target": {
            "id": CASE_ID,
            "global_case": GLOBAL_CASE,
            "local_case": LOCAL_CASE,
            "first_tree_action": {
                "kind": "Iarg_facet",
                "coordinate": 0,
                "side": "right",
                "fraction": {
                    "numerator": 1,
                    "denominator": 2,
                    "decimal": "0.5000",
                },
                "archive_index": 716,
                "leaf_index": 1311,
            },
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
        raise SystemExit("stale action-296 nonlinear target: run with --write")


if __name__ == "__main__":
    main()
