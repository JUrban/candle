#!/usr/bin/env python3
"""Prepare the clean predecessor checkpoint for first-leaf experiments.

The bundle authenticates and loads the complete nonlinear verifier closure and
the three native reconstruction modules, then stops before target
reconstruction, certificate search, Taylor construction, or formal proof.
Disposable checkpoint restores can therefore vary only the focused experiment
without replaying the analytic closure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_analytic_segmentation as analytic_segmentation
import flyspeck_nonlinear_first_leaf as first_leaf
import flyspeck_nonlinear_verifier_smoke as smoke


ROOT = Path(__file__).resolve().parents[1]
RESULT_SCHEMA = 1
POST_ANALYTIC_SOURCE_KEY = (
    "flyspeck:formal_ineqs/taylor/theory/"
    "multivariate_taylor-compiled.hl"
)
POST_ANALYTIC_CLOSURE_READY_REF = (
    "candle_nonlinear_post_analytic_closure_ready"
)


def build_post_analytic_suffix(
    candle_root: Path,
    flyspeck_root: Path,
    records: list[dict[str, Any]],
    overlays: list[dict[str, str]],
    target: dict[str, Any],
    support_records: list[dict[str, Any]],
) -> str:
    """Build the authenticated verifier/support suffix for the Taylor base.

    The input assumes only the separately authenticated post-analytic
    checkpoint contract.  It reauthenticates every source and normalized
    overlay before changing the loader tables, checks the exact analytic
    source identity already present in the restored state, and then loads the
    verifier and first-leaf support without replaying the Taylor theories.
    """

    source_rows = ";\n   ".join(
        "(%s,%s,%s)" % (
            smoke._ocaml_string(record["physical_path"]),
            smoke._ocaml_string(record["basename"]),
            smoke._ocaml_string(record["md5"]),
        )
        for record in records
    )
    overlay_rows = ";\n   ".join(
        "(%s,%s,%s)" % (
            smoke._ocaml_string(record["original_path"]),
            smoke._ocaml_string(record["normalized_path"]),
            smoke._ocaml_string(record["normalized_md5"]),
        )
        for record in overlays
    )
    analytic_record = next(
        record for record in records
        if record["source_key"] == POST_ANALYTIC_SOURCE_KEY
    )
    root_record = next(
        record for record in records
        if record["source_key"]
        == "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
    )
    analytic_identity = "(%s,%s)" % (
        smoke._ocaml_string(analytic_record["basename"]),
        smoke._ocaml_string(analytic_record["md5"]),
    )
    root_identity = "(%s,%s)" % (
        smoke._ocaml_string(root_record["basename"]),
        smoke._ocaml_string(root_record["md5"]),
    )
    candle = smoke._ocaml_string(str(candle_root.resolve()))
    flyspeck = smoke._ocaml_string(str(flyspeck_root.resolve()))
    closure_ready_ref = POST_ANALYTIC_CLOSURE_READY_REF
    suffix = f'''(* Generated DEVELOPMENT / NON-RELEASE post-analytic verifier suffix. *)
let candle_nonlinear_post_analytic_started = Unix.gettimeofday();;
let {closure_ready_ref} = ref false;;

let candle_nonlinear_post_analytic_source_rows =
  [{source_rows}];;

let candle_nonlinear_post_analytic_check_source (path,_,expected_md5) =
  if not (Sys.file_exists path) then
    failwith ("missing post-analytic source: " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected_md5 then
    failwith ("post-analytic source digest mismatch: " ^ path);;

List.iter candle_nonlinear_post_analytic_check_source
  candle_nonlinear_post_analytic_source_rows;;
Cakeml.configureSourceIdentities
  (map (fun (path,basename,digest) -> path,(basename,digest))
       candle_nonlinear_post_analytic_source_rows);;

let candle_nonlinear_post_analytic_overlay_rows =
  [{overlay_rows}];;

let candle_nonlinear_post_analytic_check_overlay (_,path,expected_md5) =
  if not (Sys.file_exists path) then
    failwith ("missing post-analytic overlay: " ^ path)
  else if Digest.to_hex (Digest.file path) <> expected_md5 then
    failwith ("post-analytic overlay digest mismatch: " ^ path);;

List.iter candle_nonlinear_post_analytic_check_overlay
  candle_nonlinear_post_analytic_overlay_rows;;
Cakeml.configureNormalizationOverlay
  (map (fun (original,normalized,_) -> original,normalized)
       candle_nonlinear_post_analytic_overlay_rows);;

if !Cakeml.pendingLoadedSourceIds <> [] ||
   not (List.mem {analytic_identity} !Cakeml.loadedSourceIds) then
  failwith "post-analytic checkpoint source identity mismatch"
else ();;

let candle_nonlinear_post_analytic_add_load_path path =
  if List.mem path !load_path then () else load_path := path :: !load_path;;
let candle_nonlinear_post_analytic_candle_root = {candle} and
    candle_nonlinear_post_analytic_flyspeck_root = {flyspeck};;
List.iter candle_nonlinear_post_analytic_add_load_path
  [candle_nonlinear_post_analytic_candle_root;
   Filename.concat candle_nonlinear_post_analytic_flyspeck_root
     "text_formalization";
   Filename.concat candle_nonlinear_post_analytic_flyspeck_root
     "formal_ineqs";
   Filename.concat candle_nonlinear_post_analytic_flyspeck_root "jHOLLight"];;

needs "arith_options.hl";;
Arith_options.base := 200;;
needs "verifier/m_verifier_main.hl";;

if !Cakeml.pendingLoadedSourceIds <> [] ||
   not (List.mem {root_identity} !Cakeml.loadedSourceIds) then
  failwith "post-analytic verifier loader identity did not commit"
else
  let _ = M_verifier_main.verify_ineq in
  ({closure_ready_ref} := true;
   print_endline "{smoke.LOAD_MARKER}";
   print_endline
     ("{smoke.CLOSURE_SECONDS} " ^
      string_of_float
        (Unix.gettimeofday() -. candle_nonlinear_post_analytic_started)));;
'''
    return suffix + first_leaf.build_target_prelude(
        target,
        flyspeck_root,
        support_records,
        first_leaf.SUPPORT_READY_MARKER,
        required_ready_ref=closure_ready_ref,
    )


def prepare(
    flyspeck_root: Path,
    runtime: Path,
    generated_insulate: Path,
    output_root: Path,
) -> dict[str, Any]:
    """Materialize one source-authenticated first-leaf predecessor bundle."""

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
    segmentation = analytic_segmentation.segment_records(closure_records)
    target_data, target, support_records = first_leaf.authenticate_target(
        flyspeck_root, closure_data,
    )
    records = closure_records + support_records
    big_int_compatibility, big_int_record = (
        smoke.authenticate_big_int_compatibility(candle_root)
    )

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
    post_analytic_suffix = output_root / "post-analytic-suffix.ml"
    setup = output_root / "setup.ml"
    driver.write_text(
        smoke.build_driver(
            candle_root,
            flyspeck_root,
            records,
            overlays,
            big_int_compatibility,
            closure_only=True,
        )
        + first_leaf.build_target_prelude(
            target,
            flyspeck_root,
            support_records,
            first_leaf.SUPPORT_READY_MARKER,
        ),
        encoding="ascii",
        newline="\n",
    )
    setup.write_text(
        smoke.build_stdin(candle_root, support_root, driver),
        encoding="ascii",
        newline="\n",
    )
    post_analytic_suffix.write_text(
        build_post_analytic_suffix(
            candle_root,
            flyspeck_root,
            records,
            overlays,
            target,
            support_records,
        ),
        encoding="ascii",
        newline="\n",
    )

    payload = {
        "schema": RESULT_SCHEMA,
        "kind": "candle-flyspeck-nonlinear-first-leaf-checkpoint-input",
        "status": "development-non-release",
        "claim": (
            "authenticated nonlinear closure and first-leaf reconstruction "
            "support input; stops before reconstruction, search, Taylor "
            "construction, or proof; not a checkpoint, proof, cumulative, "
            "S2, S3, qualification, promotion, or release result"
        ),
        "ready_marker": first_leaf.SUPPORT_READY_MARKER,
        "candle_commit": smoke._git_head(candle_root),
        "closure": {
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
            "flyspeck_commit": closure["repositories"]["flyspeck"][
                "commit"
            ],
        },
        "target": {
            "bytes": len(target_data),
            "sha256": hashlib.sha256(target_data).hexdigest(),
            "id": target["target"]["id"],
            "global_case": target["target"]["global_case"],
            "local_case": target["target"]["local_case"],
            "legacy_oracle_digest": target["native_oracle"][
                "legacy_theorem_digest"
            ],
        },
        "closure_source_node_count": len(closure_records),
        "support_source_node_count": len(support_records),
        "source_node_count": len(records),
        "normalized_source_count": len(overlays),
        "segmentation": segmentation,
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
        "big_int_compatibility": big_int_record,
        "runtime": smoke._record_file(runtime),
        "generated_insulation_input": smoke._record_file(
            generated_insulate
        ),
        "generated_insulation_support": smoke._record_file(
            support_insulate
        ),
        "controller": smoke._record_file(Path(__file__).resolve()),
        "driver": smoke._record_file(driver),
        "post_analytic_suffix": smoke._record_file(post_analytic_suffix),
        "setup": smoke._record_file(setup),
    }
    receipt = output_root / "input-receipt.json"
    with receipt.open("x", encoding="utf-8") as destination:
        json.dump(payload, destination, indent=2, sort_keys=True)
        destination.write("\n")
    return payload


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--generated-insulate", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    arguments = parser.parse_args()
    payload = prepare(
        arguments.flyspeck_root,
        arguments.runtime,
        arguments.generated_insulate,
        arguments.output_root,
    )
    print(json.dumps({
        "driver": payload["driver"],
        "ready_marker": payload["ready_marker"],
        "segmented_chunks": payload["segmentation"]["chunk_count"],
        "source_nodes": payload["source_node_count"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
