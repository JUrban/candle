#!/usr/bin/env python3
"""Run the first proof-producing Candle nonlinear-verifier gate.

The parser survey is deliberately separate from this gate.  This controller
authenticates every source in the exact verifier closure before starting a
fresh Candle process, generates a second in-process MD5 preflight, loads the
closure with the required arithmetic-base ordering, and asks
``M_verifier_main.verify_ineq`` for a small ordinary HOL theorem.

The result is DEVELOPMENT / NON-RELEASE evidence.  It is a source-load and
proof-production compatibility gate, not evidence for the substantial Azure
leaf and not S2/S3 or release evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import time
from pathlib import Path, PurePosixPath
from typing import Any

import flyspeck_nonlinear_verifier_closure


ROOT = Path(__file__).resolve().parents[1]
CLOSURE = Path("candle/flyspeck_nonlinear_verifier_closure.json")
RESULT_SCHEMA = 1
PASS_MARKER = "CANDLE_NONLINEAR_VERIFIER_SMOKE_OK"
LOAD_MARKER = "CANDLE_NONLINEAR_VERIFIER_CLOSURE_LOADED"
THEOREM_BEGIN = "CANDLE_NONLINEAR_VERIFIER_THEOREM_BEGIN"
THEOREM_END = "CANDLE_NONLINEAR_VERIFIER_THEOREM_END"
CLOSURE_SECONDS = "CANDLE_NONLINEAR_VERIFIER_CLOSURE_SECONDS"
SMOKE_PROOF_SECONDS = "CANDLE_NONLINEAR_VERIFIER_SMOKE_PROOF_SECONDS"
FORBIDDEN_LOG_BYTES = (b"Parsing failed", b"EXCEPTION:")


def _hash_file(path: Path, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def _ordinary_file(path: Path, label: str) -> None:
    if not path.is_file() or path.is_symlink():
        raise ValueError(f"{label} is not an ordinary file: {path}")


def _git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def _ocaml_string(value: str) -> str:
    # JSON's ASCII string literal syntax is accepted by OCaml for these paths.
    return json.dumps(value, ensure_ascii=True)


def _logical_path(value: object, label: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"non-string logical path: {label}")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "." in path.parts:
        raise ValueError(f"unsafe logical path: {label}: {value}")
    if not path.parts:
        raise ValueError(f"empty logical path: {label}")
    return value


def authenticate_closure(
    candle_root: Path,
    flyspeck_root: Path,
) -> tuple[bytes, dict[str, Any], list[dict[str, Any]]]:
    """Validate the complete closure and return physical identity records."""

    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    closure_path = candle_root / CLOSURE
    _ordinary_file(closure_path, "nonlinear verifier closure")
    closure_data = closure_path.read_bytes()
    closure = json.loads(closure_data)
    if (
        closure.get("schema") != 1
        or closure.get("kind")
        != "candle-flyspeck-nonlinear-verifier-source-closure"
        or closure.get("root")
        != "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
        or closure.get("counts", {}).get("selected_source_nodes") != 90
        or closure.get("counts", {}).get("identity_extension") != 56
    ):
        raise ValueError("unexpected nonlinear verifier closure contract")

    expected_flyspeck_head = closure.get("repositories", {}).get(
        "flyspeck", {},
    ).get("commit")
    if _git_head(flyspeck_root) != expected_flyspeck_head:
        raise ValueError("nonlinear verifier Flyspeck repository identity drift")

    nodes = closure.get("source_nodes")
    if not isinstance(nodes, dict) or len(nodes) != 90:
        raise ValueError("malformed nonlinear verifier source-node map")
    roots = {"candle": candle_root, "flyspeck": flyspeck_root}
    records: list[dict[str, Any]] = []
    for source_key in sorted(nodes):
        node = nodes[source_key]
        if not isinstance(node, dict):
            raise ValueError(f"malformed source node: {source_key}")
        repository = node.get("repository")
        if repository not in roots:
            raise ValueError(f"unknown source repository: {source_key}")
        logical = _logical_path(
            node.get("logical_relative_path"), source_key,
        )
        if source_key != f"{repository}:{logical}":
            raise ValueError(f"source logical identity mismatch: {source_key}")
        physical = roots[repository] / logical
        _ordinary_file(physical, f"nonlinear verifier source {source_key}")
        data = physical.read_bytes()
        md5 = hashlib.md5(data, usedforsecurity=False).hexdigest()
        sha256 = hashlib.sha256(data).hexdigest()
        if (
            len(data) != node.get("bytes")
            or md5 != node.get("md5")
            or sha256 != node.get("sha256")
        ):
            raise ValueError(f"nonlinear verifier source drift: {source_key}")
        selected = node.get("selected_dependencies")
        if not isinstance(selected, list) or any(
            dependency not in nodes for dependency in selected
        ):
            raise ValueError(f"invalid source dependency closure: {source_key}")
        normalized, normalization = (
            flyspeck_nonlinear_verifier_closure.apply_recorded_normalization(
                source_key, data, node,
            )
        )
        records.append({
            "source_key": source_key,
            "repository": repository,
            "logical_relative_path": logical,
            "physical_path": str(physical),
            "basename": physical.name,
            "bytes": str(len(data)),
            "md5": md5,
            "sha256": sha256,
            "normalization": normalization,
            "normalized_bytes": normalized,
        })
    return closure_data, closure, records


def materialize_normalizations(
    output_root: Path,
    records: list[dict[str, Any]],
) -> list[dict[str, str]]:
    """Write exact normalized overlays after the complete host preflight."""

    overlays: list[dict[str, str]] = []
    for record in records:
        normalization = record["normalization"]
        if normalization is None:
            continue
        normalized = record["normalized_bytes"]
        normalized_path = (
            output_root / "overlay" / record["repository"]
            / record["logical_relative_path"]
        )
        normalized_path.parent.mkdir(parents=True, exist_ok=True)
        with normalized_path.open("xb") as destination:
            destination.write(normalized)
        normalized_path.chmod(0o444)
        if (
            len(normalized) != normalization["normalized_bytes"]
            or hashlib.md5(
                normalized, usedforsecurity=False,
            ).hexdigest() != normalization["normalized_md5"]
            or hashlib.sha256(normalized).hexdigest()
            != normalization["normalized_sha256"]
        ):
            raise ValueError(
                f"materialized normalization drift: {record['source_key']}"
            )
        overlays.append({
            "source_key": record["source_key"],
            "original_path": record["physical_path"],
            "normalized_path": str(normalized_path),
            "normalized_md5": normalization["normalized_md5"],
            "normalized_sha256": normalization["normalized_sha256"],
        })
    return overlays


def build_driver(
    candle_root: Path,
    flyspeck_root: Path,
    records: list[dict[str, Any]],
    overlays: list[dict[str, str]],
) -> str:
    """Generate the one-file, failure-dependent source-load/proof program."""

    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    source_rows = ";\n   ".join(
        "(%s,%s,%s)" % (
            _ocaml_string(record["physical_path"]),
            _ocaml_string(record["basename"]),
            _ocaml_string(record["md5"]),
        )
        for record in records
    )
    overlay_rows = ";\n   ".join(
        "(%s,%s,%s)" % (
            _ocaml_string(record["original_path"]),
            _ocaml_string(record["normalized_path"]),
            _ocaml_string(record["normalized_md5"]),
        )
        for record in overlays
    )
    root_record = next(
        record for record in records
        if record["source_key"]
        == "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
    )
    candle = _ocaml_string(str(candle_root))
    flyspeck = _ocaml_string(str(flyspeck_root))
    root_identity = (
        f"({_ocaml_string(root_record['basename'])},"
        f"{_ocaml_string(root_record['md5'])})"
    )
    return f'''(* Generated DEVELOPMENT / NON-RELEASE nonlinear verifier gate. *)
#use "hol.ml";;

let candle_nonlinear_closure_started = Unix.gettimeofday();;

let candle_nonlinear_source_rows =
  [{source_rows}];;

let candle_nonlinear_check_source (path,_,expected_md5) =
  if not (Sys.file_exists path) then
    failwith ("missing nonlinear verifier source: " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected_md5 then
    failwith ("nonlinear verifier source digest mismatch: " ^ path);;

(* Every source is checked before any new verifier source is parsed/evaluated. *)
List.iter candle_nonlinear_check_source candle_nonlinear_source_rows;;

Cakeml.configureSourceIdentities
  (map (fun (path,basename,digest) -> path,(basename,digest))
       candle_nonlinear_source_rows);;

let candle_nonlinear_overlay_rows =
  [{overlay_rows}];;

let candle_nonlinear_check_overlay (_,path,expected_md5) =
  if not (Sys.file_exists path) then
    failwith ("missing nonlinear verifier overlay: " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected_md5 then
    failwith ("nonlinear verifier overlay digest mismatch: " ^ path);;

List.iter candle_nonlinear_check_overlay candle_nonlinear_overlay_rows;;
Cakeml.configureNormalizationOverlay
  (map (fun (original,normalized,_) -> original,normalized)
       candle_nonlinear_overlay_rows);;

let candle_nonlinear_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;

let candle_nonlinear_candle_root = {candle} and
    candle_nonlinear_flyspeck_root = {flyspeck};;

List.iter candle_nonlinear_add_load_path
  [candle_nonlinear_candle_root;
   Filename.concat candle_nonlinear_flyspeck_root "text_formalization";
   Filename.concat candle_nonlinear_flyspeck_root "formal_ineqs";
   Filename.concat candle_nonlinear_flyspeck_root "jHOLLight"];;

(* This order is semantically required by formal_ineqs/arith/arith_num.hl. *)
needs "arith_options.hl";;
Arith_options.base := 200;;
needs "verifier/m_verifier_main.hl";;

if !Cakeml.pendingLoadedSourceIds <> [] ||
   not (List.mem {root_identity} !Cakeml.loadedSourceIds) then
  failwith "nonlinear verifier loader identity did not commit";;

print_endline "{LOAD_MARKER}";;
print_endline
  (Printf.sprintf "{CLOSURE_SECONDS} %.6f"
     (Unix.gettimeofday() -. candle_nonlinear_closure_started));;

open M_verifier_main;;
Verifier_options.info_print_level := 0;;
let candle_nonlinear_smoke_term =
  `&0 <= x /\\ x <= &1 ==> x < #1.5`;;
let candle_nonlinear_axioms_before = axioms ();;
let candle_nonlinear_smoke_started = Unix.gettimeofday();;
let candle_nonlinear_smoke_theorem,candle_nonlinear_smoke_stats =
  verify_ineq {{default_params with eps = 1e-10}} 6
    candle_nonlinear_smoke_term;;
print_endline
  (Printf.sprintf "{SMOKE_PROOF_SECONDS} %.6f"
     (Unix.gettimeofday() -. candle_nonlinear_smoke_started));;

if hyp candle_nonlinear_smoke_theorem <> [] ||
   concl candle_nonlinear_smoke_theorem <> candle_nonlinear_smoke_term then
  failwith "nonlinear verifier smoke theorem interface mismatch";;

let candle_nonlinear_axioms_after = axioms ();;
if List.length candle_nonlinear_axioms_after <>
     List.length candle_nonlinear_axioms_before ||
   not (List.for_all
          (fun th -> List.mem th candle_nonlinear_axioms_before)
          candle_nonlinear_axioms_after) then
  failwith "nonlinear verifier smoke changed the global axiom set";;

print_endline "{THEOREM_BEGIN}";;
print_thm candle_nonlinear_smoke_theorem;;
print_endline "{THEOREM_END}";;
print_endline "{PASS_MARKER}";;
'''


def _record_file(path: Path) -> dict[str, Any]:
    return {
        "path": str(path),
        "bytes": path.stat().st_size,
        "sha256": _hash_file(path, "sha256"),
    }


def _extract_seconds(log_data: bytes, marker: str) -> float | None:
    matches = re.findall(
        rb"^" + re.escape(marker.encode("ascii"))
        + rb" ([0-9]+(?:\.[0-9]+)?)$",
        log_data,
        flags=re.MULTILINE,
    )
    if len(matches) != 1:
        return None
    return float(matches[0])


def run(
    flyspeck_root: Path,
    runtime: Path,
    generated_insulate: Path,
    output_root: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    candle_root = ROOT.resolve()
    flyspeck_root = flyspeck_root.resolve()
    runtime = runtime.resolve()
    generated_insulate = generated_insulate.resolve()
    output_root = output_root.resolve()
    if output_root.exists():
        raise ValueError(f"output root already exists: {output_root}")
    _ordinary_file(runtime, "Candle runtime")
    _ordinary_file(
        generated_insulate, "Candle generated insulation support",
    )
    closure_data, closure, records = authenticate_closure(
        candle_root, flyspeck_root,
    )

    output_root.mkdir(parents=True)
    overlays = materialize_normalizations(output_root, records)
    support_root = output_root / "base-support"
    support_insulate = support_root / "candle/build/insulate.ml"
    support_insulate.parent.mkdir(parents=True)
    with support_insulate.open("xb") as destination:
        destination.write(generated_insulate.read_bytes())
    support_insulate.chmod(0o444)
    if (
        support_insulate.stat().st_size != generated_insulate.stat().st_size
        or _hash_file(support_insulate, "sha256")
        != _hash_file(generated_insulate, "sha256")
    ):
        raise ValueError("materialized generated insulation support drift")
    driver = output_root / "driver.ml"
    stdin = output_root / "stdin.ml"
    log = output_root / "candle.log"
    driver.write_text(
        build_driver(candle_root, flyspeck_root, records, overlays),
        encoding="ascii", newline="\n",
    )
    stdin.write_text(
        f'Cakeml.loadPath := [{_ocaml_string(str(candle_root))}; '
        f'{_ocaml_string(str(support_root))}];;\n'
        f'#use {_ocaml_string(str(driver))};;\n',
        encoding="ascii", newline="\n",
    )

    candle_commit = _git_head(candle_root)
    runtime_record = _record_file(runtime)
    generated_insulation_input_record = _record_file(generated_insulate)
    generated_insulation_support_record = _record_file(support_insulate)
    controller_record = _record_file(Path(__file__).resolve())
    driver_record = _record_file(driver)
    stdin_record = _record_file(stdin)

    started_utc = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    started = time.monotonic()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    timed_out = False
    with stdin.open("rb") as source, log.open("xb") as transcript:
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
            return_code: int | None = completed.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            return_code = None
    elapsed = time.monotonic() - started
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    log_data = log.read_bytes()
    markers = {
        "closure_loaded": log_data.count((LOAD_MARKER + "\n").encode()),
        "theorem_begin": log_data.count((THEOREM_BEGIN + "\n").encode()),
        "theorem_end": log_data.count((THEOREM_END + "\n").encode()),
        "pass": log_data.count((PASS_MARKER + "\n").encode()),
    }
    forbidden = [
        value.decode("ascii") for value in FORBIDDEN_LOG_BYTES
        if value in log_data
    ]
    timings = {
        "closure_seconds": _extract_seconds(log_data, CLOSURE_SECONDS),
        "smoke_proof_seconds": _extract_seconds(
            log_data, SMOKE_PROOF_SECONDS,
        ),
    }
    outcome = (
        "proof-pass"
        if not timed_out
        and return_code == 0
        and markers == {
            "closure_loaded": 1,
            "theorem_begin": 1,
            "theorem_end": 1,
            "pass": 1,
        }
        and all(value is not None for value in timings.values())
        and not forbidden
        else "proof-failure"
    )
    payload = {
        "schema": RESULT_SCHEMA,
        "kind": "candle-flyspeck-nonlinear-verifier-smoke-result",
        "status": "development-non-release",
        "claim": (
            "authenticated fresh source load and small proof-producing "
            "compatibility gate; no substantial leaf, S2, S3, qualification, "
            "promotion, or release credit"
        ),
        "started_utc": started_utc,
        "outcome": outcome,
        "timed_out": timed_out,
        "exit_code": return_code,
        "elapsed_seconds": elapsed,
        "child_user_seconds": usage_after.ru_utime - usage_before.ru_utime,
        "child_system_seconds": usage_after.ru_stime - usage_before.ru_stime,
        "child_max_rss_kib": usage_after.ru_maxrss,
        "markers": markers,
        "timings": timings,
        "forbidden_log_fragments": forbidden,
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
            "path": CLOSURE.as_posix(),
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"]["commit"],
        },
        "candle_commit": candle_commit,
        "runtime": runtime_record,
        "generated_insulation_input": generated_insulation_input_record,
        "generated_insulation_support": generated_insulation_support_record,
        "controller": controller_record,
        "driver": driver_record,
        "stdin": stdin_record,
        "log": _record_file(log),
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
    parser.add_argument("--timeout-seconds", type=int, default=43200)
    arguments = parser.parse_args()
    payload = run(
        arguments.flyspeck_root,
        arguments.runtime,
        arguments.generated_insulate,
        arguments.output_root,
        arguments.timeout_seconds,
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
