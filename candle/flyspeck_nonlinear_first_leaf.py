#!/usr/bin/env python3
"""Run the first substantial Flyspeck nonlinear leaf in Candle.

This DEVELOPMENT / NON-RELEASE controller extends the authenticated nonlinear
verifier smoke gate with the exact native-Flyspeck reconstruction interface.
It does not trust the retained native theorem: that record only supplies the
target term.  Candle must reconstruct the leaf and return an ordinary kernel
theorem with the exact target conclusion, no hypotheses, and no new axioms.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import resource
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_first_leaf_target as target_authority
import flyspeck_nonlinear_closure_profile as closure_profile
import flyspeck_nonlinear_first_leaf_profile as phase_profile
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
TARGET = Path("candle/flyspeck_nonlinear_first_leaf_target.json")
RESULT_SCHEMA = 1
RECONSTRUCTION_BEGIN = "CANDLE_NONLINEAR_FIRST_LEAF_RECONSTRUCTION_BEGIN"
RECONSTRUCTION_END = "CANDLE_NONLINEAR_FIRST_LEAF_RECONSTRUCTION_END"
THEOREM_BEGIN = "CANDLE_NONLINEAR_FIRST_LEAF_THEOREM_BEGIN"
THEOREM_END = "CANDLE_NONLINEAR_FIRST_LEAF_THEOREM_END"
PASS_MARKER = "CANDLE_NONLINEAR_FIRST_LEAF_OK"
RECONSTRUCTION_SECONDS = "CANDLE_NONLINEAR_FIRST_LEAF_RECONSTRUCTION_SECONDS"
VERIFICATION_SECONDS = "CANDLE_NONLINEAR_FIRST_LEAF_VERIFICATION_SECONDS"
VERIFIER_REPORTED_SECONDS = "CANDLE_NONLINEAR_FIRST_LEAF_VERIFIER_SECONDS"
FORMAL_VERIFICATION_SECONDS = (
    "CANDLE_NONLINEAR_FIRST_LEAF_FORMAL_VERIFICATION_SECONDS"
)
MODULE_NORMALIZATION = "candle-native-module-wrapper-v1"
PHASE_OBSERVER = Path("candle/compatibility/certificate_phase_profile.py")
PHASE_PROFILE_STOP_KEY = "nonlinear-leaf/target/total"
EXPECTED_PHASE_COUNTS = {
    ("verify-call", "standardize"): 2,
    ("verify-call", "problem-reification"): 1,
    ("verify-call", "evaluator-build"): 1,
    ("verify-call", "informal-search"): 1,
    ("verify-call", "adaptive-informal-verification"): 1,
    ("verify-call", "formal-verification"): 1,
    ("verify-call", "final-normalization"): 1,
    ("target", "total"): 1,
}
EXPECTED_PHASE_COUNTS.update({
    (f"formal-leaf-{index}", "leaf-check"): 1
    for index in range(1, 17)
})
EXPECTED_PHASE_COUNTS.update({
    (f"formal-glue-{index}", phase): 1
    for index in range(1, 16)
    for phase in ("domain-split", "theorem-glue")
})

SUPPORT = {
    "prove_by_refinement": (
        target_authority.PROVE_BY_REFINEMENT,
        None,
        b"",
    ),
    "compiled_definitions": (
        target_authority.COMPILED_DEFINITIONS,
        "Definitions",
        b"open Hol_core;;\n",
    ),
    "compiled_break_case": (
        target_authority.COMPILED_BREAK_CASE,
        "Break_case",
        (
            b"open Hol_core\nopen Misc\n"
        ),
    ),
}


def _record_bytes(data: bytes) -> dict[str, Any]:
    return {
        "bytes": len(data),
        "md5": hashlib.md5(data, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _module_wrapper(
    source: bytes,
    module: str,
    removable_prefix: bytes,
) -> bytes:
    if removable_prefix and not source.startswith(removable_prefix):
        raise ValueError(f"native module prelude drift: {module}")
    body = source[len(removable_prefix):]
    return (
        f"module {module} = struct\n".encode("ascii")
        + body
        + b"\nend;;\n"
    )


def authenticate_target(
    flyspeck_root: Path,
    closure_data: bytes,
) -> tuple[bytes, dict[str, Any], list[dict[str, Any]]]:
    """Authenticate the published target and prepare exact module overlays."""

    flyspeck_root = flyspeck_root.resolve()
    target_path = ROOT / TARGET
    smoke._ordinary_file(target_path, "nonlinear first-leaf target")
    target_data = target_path.read_bytes()
    target = json.loads(target_data)
    if (
        target.get("schema") != 1
        or target.get("kind")
        != "candle-flyspeck-nonlinear-first-leaf-target"
        or target.get("status") != "development-non-release"
        or target.get("target", {}).get("id") != target_authority.CASE_ID
        or target.get("target", {}).get("global_case")
        != target_authority.GLOBAL_CASE
        or target.get("target", {}).get("local_case")
        != target_authority.LOCAL_CASE
    ):
        raise ValueError("unexpected nonlinear first-leaf target contract")
    if (
        target.get("closure", {}).get("bytes") != len(closure_data)
        or target.get("closure", {}).get("sha256")
        != hashlib.sha256(closure_data).hexdigest()
    ):
        raise ValueError("first-leaf target closure identity drift")

    evidence = target.get("evidence_files")
    if not isinstance(evidence, dict) or not set(SUPPORT) <= set(evidence):
        raise ValueError("first-leaf reconstruction support is incomplete")
    records: list[dict[str, Any]] = []
    for role, (relative, module, removable_prefix) in SUPPORT.items():
        authority = evidence[role]
        if authority.get("logical_relative_path") != relative.as_posix():
            raise ValueError(f"first-leaf support path drift: {role}")
        physical = flyspeck_root / relative
        smoke._ordinary_file(physical, f"first-leaf support {role}")
        source = physical.read_bytes()
        source_identity = _record_bytes(source)
        if (
            authority.get("bytes") != source_identity["bytes"]
            or authority.get("sha256") != source_identity["sha256"]
        ):
            raise ValueError(f"first-leaf support identity drift: {role}")
        if module is None:
            normalized = source
            normalization = None
        else:
            normalized = _module_wrapper(source, module, removable_prefix)
            normalized_identity = _record_bytes(normalized)
            normalization = {
                "id": MODULE_NORMALIZATION,
                "semantic_rule": (
                    "wrap the authenticated native compilation unit in its "
                    "original module name, removing only unavailable compiled-"
                    "environment open directives while retaining its required "
                    "Flyspeck module opens"
                ),
                "role": role,
                "module": module,
                "removed_prefix_bytes": len(removable_prefix),
                "normalized_bytes": normalized_identity["bytes"],
                "normalized_md5": normalized_identity["md5"],
                "normalized_sha256": normalized_identity["sha256"],
            }
        records.append({
            "source_key": f"flyspeck:{relative.as_posix()}",
            "repository": "flyspeck",
            "logical_relative_path": relative.as_posix(),
            "physical_path": str(physical),
            "basename": physical.name,
            "bytes": str(source_identity["bytes"]),
            "md5": source_identity["md5"],
            "sha256": source_identity["sha256"],
            "normalization": normalization,
            "normalized_bytes": normalized,
        })
    return target_data, target, records


def build_target_driver(
    target: dict[str, Any],
    flyspeck_root: Path,
    support_records: list[dict[str, Any]],
    profile_phases: bool = False,
) -> str:
    theorem_text = target["target"]["legacy_ineqm_text"]
    if not isinstance(theorem_text, str) or "`" in theorem_text:
        raise ValueError("unsafe first-leaf target term")
    flyspeck_root_literal = smoke._ocaml_string(str(flyspeck_root.resolve()))
    support_ids = ";\n   ".join(
        "(%s,%s)" % (
            smoke._ocaml_string(record["basename"]),
            smoke._ocaml_string(record["md5"]),
        )
        for record in support_records
    )
    profile_begin = (
        'candle_nonlinear_profile_marker "target" "total" "begin";;'
        if profile_phases else ""
    )
    profile_end = (
        'candle_nonlinear_profile_marker "target" "total" "end";;'
        if profile_phases else ""
    )
    return f'''

let candle_nonlinear_first_leaf_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;
candle_nonlinear_first_leaf_add_load_path {flyspeck_root_literal};;

needs "{target_authority.PROVE_BY_REFINEMENT.as_posix()}";;
needs "{target_authority.COMPILED_DEFINITIONS.as_posix()}";;
needs "{target_authority.COMPILED_BREAK_CASE.as_posix()}";;

let candle_nonlinear_first_leaf_support_ids =
  [{support_ids}];;
if !Cakeml.pendingLoadedSourceIds <> [] ||
   not (List.for_all
          (fun source_id -> List.mem source_id !Cakeml.loadedSourceIds)
          candle_nonlinear_first_leaf_support_ids) then
  failwith "first-leaf support loader identity did not commit";;

let candle_nonlinear_first_leaf_target =
  `{theorem_text}`;;

let candle_nonlinear_first_leaf_axioms_before = axioms ();;
print_endline "{RECONSTRUCTION_BEGIN}";;
let candle_nonlinear_first_leaf_reconstruction_started = Unix.gettimeofday();;
let candle_nonlinear_first_leaf_eq =
  Break_case.ineqm_conv candle_nonlinear_first_leaf_target;;
let candle_nonlinear_first_leaf_reconstruction_seconds =
  Unix.gettimeofday() -. candle_nonlinear_first_leaf_reconstruction_started;;
print_endline
  ("{RECONSTRUCTION_SECONDS} " ^
   string_of_float candle_nonlinear_first_leaf_reconstruction_seconds);;
print_endline "{RECONSTRUCTION_END}";;

if lhand (concl candle_nonlinear_first_leaf_eq) <>
     candle_nonlinear_first_leaf_target then
  failwith "first-leaf reconstruction source interface mismatch";;

let candle_nonlinear_first_leaf_converted =
  rand (concl candle_nonlinear_first_leaf_eq);;
let candle_nonlinear_first_leaf_verification_started = Unix.gettimeofday();;
{profile_begin}
let candle_nonlinear_first_leaf_raw,candle_nonlinear_first_leaf_stats =
  M_verifier_main.verify_ineq
    {{M_verifier_main.default_params with eps = 1e-10}} 6
    candle_nonlinear_first_leaf_converted;;
{profile_end}
let candle_nonlinear_first_leaf_verification_seconds =
  Unix.gettimeofday() -. candle_nonlinear_first_leaf_verification_started;;
print_endline
  ("{VERIFICATION_SECONDS} " ^
   string_of_float candle_nonlinear_first_leaf_verification_seconds);;
print_endline
  ("{VERIFIER_REPORTED_SECONDS} " ^
   string_of_float candle_nonlinear_first_leaf_stats.total_time);;
print_endline
  ("{FORMAL_VERIFICATION_SECONDS} " ^
   string_of_float
     candle_nonlinear_first_leaf_stats.formal_verification_time);;

let candle_nonlinear_first_leaf_specialized =
  SPEC_ALL candle_nonlinear_first_leaf_raw;;
let candle_nonlinear_first_leaf_implication =
  mk_imp
    (concl candle_nonlinear_first_leaf_specialized,
     candle_nonlinear_first_leaf_converted);;
let candle_nonlinear_first_leaf_implication_thm =
  TAUT candle_nonlinear_first_leaf_implication;;
let candle_nonlinear_first_leaf_converted_thm =
  MP candle_nonlinear_first_leaf_implication_thm
     candle_nonlinear_first_leaf_specialized;;
let candle_nonlinear_first_leaf_theorem =
  REWRITE_RULE[GSYM candle_nonlinear_first_leaf_eq]
    candle_nonlinear_first_leaf_converted_thm;;

if hyp candle_nonlinear_first_leaf_theorem <> [] ||
   concl candle_nonlinear_first_leaf_theorem <>
     candle_nonlinear_first_leaf_target then
  failwith "first-leaf theorem interface mismatch";;

let candle_nonlinear_first_leaf_axioms_after = axioms ();;
if List.length candle_nonlinear_first_leaf_axioms_after <>
     List.length candle_nonlinear_first_leaf_axioms_before ||
   not (List.for_all
          (fun th -> List.mem th candle_nonlinear_first_leaf_axioms_before)
          candle_nonlinear_first_leaf_axioms_after) then
  failwith "first-leaf verification changed the global axiom set";;

print_endline "{THEOREM_BEGIN}";;
print_thm candle_nonlinear_first_leaf_theorem;;
print_endline "{THEOREM_END}";;
print_endline "{PASS_MARKER}";;
'''


def _extract_seconds(log_data: bytes, marker: str) -> float | None:
    matches = re.findall(
        rb"^" + re.escape(marker.encode("ascii"))
        + rb" ([-+]?[0-9]+(?:\.[0-9]*)?(?:[eE][-+]?[0-9]+)?)$",
        log_data,
        flags=re.MULTILINE,
    )
    if len(matches) != 1:
        return None
    return float(matches[0])


def _validate_phase_profile(data: dict[str, Any]) -> tuple[dict[str, Any], bool]:
    counts: dict[tuple[str, str], int] = {}
    all_ended = True
    all_lanes_match = True
    for phase in data.get("phases", []):
        key = (phase.get("scope"), phase.get("phase"))
        counts[key] = counts.get(key, 0) + 1
        all_ended = all_ended and phase.get("result") == "end"
        all_lanes_match = (
            all_lanes_match and phase.get("lane") == "nonlinear-leaf"
        )
    expected = {
        f"{scope}/{phase}": count
        for (scope, phase), count in EXPECTED_PHASE_COUNTS.items()
    }
    observed = {
        f"{scope}/{phase}": count
        for (scope, phase), count in sorted(counts.items())
    }
    complete = (
        data.get("schema") == "candle-certificate-phase-profile-v1"
        and data.get("stop_key") == PHASE_PROFILE_STOP_KEY
        and data.get("stop_seen") is True
        and data.get("unclosed_phases") == []
        and all_ended
        and all_lanes_match
        and counts == EXPECTED_PHASE_COUNTS
    )
    return {
        "schema": data.get("schema"),
        "stop_seen": data.get("stop_seen"),
        "unclosed_phases": data.get("unclosed_phases"),
        "all_lanes_match": all_lanes_match,
        "event_count": len(data.get("events", [])),
        "phase_count": len(data.get("phases", [])),
        "peak_sampled_rss_kib": data.get("peak_sampled_rss_kib"),
        "expected_phase_counts": expected,
        "observed_phase_counts": observed,
    }, complete


def run(
    flyspeck_root: Path,
    runtime: Path,
    generated_insulate: Path,
    output_root: Path,
    timeout_seconds: int,
    profile_phases: bool = False,
    profile_closure: bool = False,
) -> dict[str, Any]:
    candle_root = ROOT.resolve()
    flyspeck_root = flyspeck_root.resolve()
    runtime = runtime.resolve()
    generated_insulate = generated_insulate.resolve()
    output_root = output_root.resolve()
    if output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")
    smoke._ordinary_file(runtime, "Candle runtime")
    smoke._ordinary_file(
        generated_insulate, "Candle generated insulation support",
    )
    closure_data, closure, closure_records = smoke.authenticate_closure(
        candle_root, flyspeck_root,
    )
    phase_profile_receipt = (
        phase_profile.instrument_records(closure_records)
        if profile_phases else None
    )
    closure_profile_receipt = (
        closure_profile.instrument_records(closure_records)
        if profile_closure else None
    )
    big_int_compatibility, big_int_compatibility_record = (
        smoke.authenticate_big_int_compatibility(candle_root)
    )
    target_data, target, support_records = authenticate_target(
        flyspeck_root, closure_data,
    )
    records = closure_records + support_records

    output_root.mkdir(parents=True)
    overlays = smoke.materialize_normalizations(output_root, records)
    support_root = output_root / "base-support"
    support_insulate = support_root / "candle/build/insulate.ml"
    support_insulate.parent.mkdir(parents=True)
    with support_insulate.open("xb") as destination:
        destination.write(generated_insulate.read_bytes())
    support_insulate.chmod(0o444)
    if smoke._hash_file(support_insulate, "sha256") != smoke._hash_file(
        generated_insulate, "sha256",
    ):
        raise ValueError("materialized generated insulation support drift")

    driver = output_root / "driver.ml"
    stdin = output_root / "stdin.ml"
    log = output_root / "candle.log"
    target_driver = build_target_driver(
        target, flyspeck_root, support_records, profile_phases,
    )
    driver.write_text(
        smoke.build_driver(
            candle_root, flyspeck_root, records, overlays,
            big_int_compatibility,
        )
        + target_driver,
        encoding="ascii",
        newline="\n",
    )
    stdin.write_text(
        smoke.build_stdin(candle_root, support_root, driver),
        encoding="ascii",
        newline="\n",
    )

    fixed_records = {
        "runtime": smoke._record_file(runtime),
        "generated_insulation_input": smoke._record_file(generated_insulate),
        "generated_insulation_support": smoke._record_file(support_insulate),
        "controller": smoke._record_file(Path(__file__).resolve()),
        "driver": smoke._record_file(driver),
        "stdin": smoke._record_file(stdin),
    }
    candle_commit = smoke._git_head(candle_root)
    started_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    started = time.monotonic()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    timed_out = False
    phase_profile_path = output_root / "phase-profile.json"
    phase_observer_log = output_root / "phase-observer.log"
    phase_observer_status: int | None = None
    with stdin.open("rb") as source, log.open("xb") as transcript:
        if profile_phases:
            observer_script = (candle_root / PHASE_OBSERVER).resolve()
            smoke._ordinary_file(observer_script, "nonlinear phase observer")
            process = subprocess.Popen(
                [str(runtime), "--candle"],
                stdin=source,
                stdout=transcript,
                stderr=subprocess.STDOUT,
                cwd=runtime.parent,
                env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
            )
            with phase_observer_log.open("xb") as observer_transcript:
                observer = subprocess.Popen(
                    [
                        sys.executable,
                        str(observer_script),
                        "--pid", str(process.pid),
                        "--log", str(log),
                        "--output", str(phase_profile_path),
                        "--poll-seconds", "0.25",
                        "--stop-key", PHASE_PROFILE_STOP_KEY,
                        "--wait-for-log-seconds", "10",
                    ],
                    stdin=subprocess.DEVNULL,
                    stdout=observer_transcript,
                    stderr=subprocess.STDOUT,
                    cwd=candle_root,
                    env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
                )
                try:
                    return_code = process.wait(timeout=timeout_seconds)
                except subprocess.TimeoutExpired:
                    timed_out = True
                    process.kill()
                    process.wait()
                    return_code = None
                try:
                    phase_observer_status = observer.wait(timeout=120)
                except subprocess.TimeoutExpired:
                    observer.kill()
                    observer.wait()
                    phase_observer_status = None
        else:
            try:
                completed = subprocess.run(
                    [str(runtime), "--candle"],
                    stdin=source,
                    stdout=transcript,
                    stderr=subprocess.STDOUT,
                    cwd=runtime.parent,
                    env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
                    timeout=timeout_seconds,
                    check=False,
                )
                return_code = completed.returncode
            except subprocess.TimeoutExpired:
                timed_out = True
                return_code = None
    elapsed = time.monotonic() - started
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    log_data = log.read_bytes()
    markers = {
        "closure_loaded": log_data.count(
            (smoke.LOAD_MARKER + "\n").encode(),
        ),
        "smoke_pass": log_data.count(
            (smoke.PASS_MARKER + "\n").encode(),
        ),
        "smoke_theorem_begin": log_data.count(
            (smoke.THEOREM_BEGIN + "\n").encode(),
        ),
        "smoke_theorem_end": log_data.count(
            (smoke.THEOREM_END + "\n").encode(),
        ),
        "reconstruction_begin": log_data.count(
            (RECONSTRUCTION_BEGIN + "\n").encode(),
        ),
        "reconstruction_end": log_data.count(
            (RECONSTRUCTION_END + "\n").encode(),
        ),
        "theorem_begin": log_data.count((THEOREM_BEGIN + "\n").encode()),
        "theorem_end": log_data.count((THEOREM_END + "\n").encode()),
        "pass": log_data.count((PASS_MARKER + "\n").encode()),
    }
    closure_markers = {
        "module_frontend_begin": log_data.count(
            b"CANDLE_NONLINEAR_TAYLOR stage=module-frontend event=begin\n"
        ),
        "module_execution_begin": log_data.count(
            b"CANDLE_NONLINEAR_TAYLOR stage=module-execution event=begin\n"
        ),
        "module_execution_end": log_data.count(
            b"CANDLE_NONLINEAR_TAYLOR stage=module-execution event=end\n"
        ),
        "module_frontend_end": log_data.count(
            b"CANDLE_NONLINEAR_TAYLOR stage=module-frontend event=end\n"
        ),
        "section_events": log_data.count(
            b"CANDLE_NONLINEAR_TAYLOR stage=section "
        ),
    }
    expected_markers = {name: 1 for name in markers}
    forbidden = [
        value.decode("ascii") for value in smoke.FORBIDDEN_LOG_BYTES
        if value in log_data
    ]
    timings = {
        "closure_seconds": _extract_seconds(
            log_data, smoke.CLOSURE_SECONDS,
        ),
        "smoke_proof_seconds": _extract_seconds(
            log_data, smoke.SMOKE_PROOF_SECONDS,
        ),
        "reconstruction_seconds": _extract_seconds(
            log_data, RECONSTRUCTION_SECONDS,
        ),
        "verification_seconds": _extract_seconds(
            log_data, VERIFICATION_SECONDS,
        ),
        "verifier_reported_seconds": _extract_seconds(
            log_data, VERIFIER_REPORTED_SECONDS,
        ),
        "formal_verification_seconds": _extract_seconds(
            log_data, FORMAL_VERIFICATION_SECONDS,
        ),
    }
    phase_profile_summary = None
    phase_profile_ok = not profile_phases
    if profile_phases and phase_profile_path.exists():
        phase_data = json.loads(phase_profile_path.read_bytes())
        phase_profile_summary, phase_content_ok = _validate_phase_profile(
            phase_data
        )
        phase_profile_ok = (
            phase_observer_status == 0
            and phase_content_ok
        )
    phase_artifacts: dict[str, Any] = {}
    if profile_phases:
        phase_artifacts["phase_observer"] = smoke._record_file(
            (candle_root / PHASE_OBSERVER).resolve()
        )
        phase_artifacts["phase_observer_log"] = smoke._record_file(
            phase_observer_log
        )
        if phase_profile_path.exists():
            phase_artifacts["phase_profile"] = smoke._record_file(
                phase_profile_path
            )
    outcome = (
        "proof-pass"
        if not timed_out
        and return_code == 0
        and markers == expected_markers
        and all(value is not None for value in timings.values())
        and phase_profile_ok
        and not forbidden
        else "proof-failure"
    )
    payload = {
        "schema": RESULT_SCHEMA,
        "kind": "candle-flyspeck-nonlinear-first-leaf-result",
        "status": "development-non-release",
        "claim": (
            "authenticated substantial first-leaf reconstruction and "
            "proof-producing verification; no cumulative, S2, S3, "
            "qualification, promotion, or release credit"
        ),
        "started_utc": started_utc,
        "outcome": outcome,
        "timed_out": timed_out,
        "exit_code": return_code,
        "elapsed_seconds": elapsed,
        "child_user_seconds": usage_after.ru_utime - usage_before.ru_utime,
        "child_system_seconds": usage_after.ru_stime - usage_before.ru_stime,
        "child_max_rss_kib": usage_after.ru_maxrss,
        "timings": timings,
        "markers": markers,
        "forbidden_log_fragments": forbidden,
        "phase_profile_enabled": profile_phases,
        "phase_profile_receipt": phase_profile_receipt,
        "phase_profile_summary": phase_profile_summary,
        "phase_observer_status": phase_observer_status,
        "closure_profile_enabled": profile_closure,
        "closure_profile_receipt": closure_profile_receipt,
        "closure_profile_markers": closure_markers,
        "source_node_count": len(records),
        "normalized_source_count": len(overlays),
        "normalized_sources": [
            {
                "source_key": overlay["source_key"],
                "normalized_path": overlay["normalized_path"],
                "normalized_md5": overlay["normalized_md5"],
                "normalized_sha256": overlay["normalized_sha256"],
            }
            for overlay in overlays
        ],
        "closure": {
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"]["commit"],
        },
        "target": {
            "path": TARGET.as_posix(),
            "bytes": len(target_data),
            "sha256": hashlib.sha256(target_data).hexdigest(),
            "id": target["target"]["id"],
            "global_case": target["target"]["global_case"],
            "local_case": target["target"]["local_case"],
            "legacy_oracle_digest": target["native_oracle"][
                "legacy_theorem_digest"
            ],
        },
        "target_support": [
            {
                "source_key": record["source_key"],
                "physical_path": record["physical_path"],
                "bytes": int(record["bytes"]),
                "md5": record["md5"],
                "sha256": record["sha256"],
                "normalization": record["normalization"],
            }
            for record in support_records
        ],
        "big_int_compatibility": big_int_compatibility_record,
        "candle_commit": candle_commit,
        **fixed_records,
        **phase_artifacts,
        "log": smoke._record_file(log),
    }
    result_path = output_root / "result.json"
    with result_path.open("x", encoding="utf-8") as destination:
        json.dump(payload, destination, indent=2, sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--generated-insulate", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=int, default=86400)
    parser.add_argument("--phase-profile", action="store_true")
    parser.add_argument("--closure-profile", action="store_true")
    arguments = parser.parse_args()
    payload = run(
        arguments.flyspeck_root,
        arguments.runtime,
        arguments.generated_insulate,
        arguments.output_root,
        arguments.timeout_seconds,
        arguments.phase_profile,
        arguments.closure_profile,
    )
    print(json.dumps({
        "outcome": payload["outcome"],
        "elapsed_seconds": payload["elapsed_seconds"],
        "result": str(arguments.output_root.resolve() / "result.json"),
    }, sort_keys=True))
    if payload["outcome"] != "proof-pass":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
