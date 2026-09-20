#!/usr/bin/env python3
"""Fail-closed phase instrumentation for the nonlinear first-leaf verifier.

The selected Candle runtime intentionally exposes no wall clock to HOL code.
This development-only normalization inserts flushed markers around the real
verifier phases; an external read-only observer supplies the timestamps and
process telemetry.  The markers neither construct nor authorize a theorem.
"""

from __future__ import annotations

import hashlib
from typing import Any


SOURCE_KEY = "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
INPUT_SHA256 = "e1c689bea39ebb4a0161816c59cf469a2f983c5705d1b392b79a555d38247dbb"
NORMALIZATION_ID = "candle-nonlinear-first-leaf-phase-profile-v1"
MARKER_PREFIX = "CANDLE_CERT_PROFILE lane=nonlinear-leaf"


def _replace_once(data: bytes, before: bytes, after: bytes, label: str) -> bytes:
    count = data.count(before)
    if count != 1:
        raise ValueError(
            f"nonlinear profile anchor drift: {label}: expected 1, got {count}"
        )
    return data.replace(before, after, 1)


def instrument_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Instrument the exact normalized verifier source and update its identity."""

    matches = [record for record in records if record["source_key"] == SOURCE_KEY]
    if len(matches) != 1:
        raise ValueError("nonlinear profile source identity is absent or duplicated")
    record = matches[0]
    data = record["normalized_bytes"]
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise ValueError("nonlinear profile normalized source identity drift")

    marker_definition = b'''open Verifier_options;;

let candle_nonlinear_profile_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=nonlinear-leaf scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;
'''
    data = _replace_once(
        data,
        b"open Verifier_options;;\n",
        marker_definition,
        "marker-definition",
    )
    data = _replace_once(
        data,
        b'''let verify_disj_ineq0 params0 norm_flag pp ineq_tm var_names (lo_tm, hi_tm) rewrite_thms =
  let total_start = Unix.gettimeofday() in
  let imp_th1 = mk_standard_ineq rewrite_thms ineq_tm in
  let ineq_tms = striplist dest_disj ((lhand o concl) imp_th1) in
''',
        b'''let verify_disj_ineq0 params0 norm_flag pp ineq_tm var_names (lo_tm, hi_tm) rewrite_thms =
  let total_start = Unix.gettimeofday() in
  let _ = candle_nonlinear_profile_marker "verify-call" "standardize" "begin" in
  let imp_th1 = mk_standard_ineq rewrite_thms ineq_tm in
  let ineq_tms = striplist dest_disj ((lhand o concl) imp_th1) in
  let _ = candle_nonlinear_profile_marker "verify-call" "standardize" "end" in
''',
        "standardize",
    )
    data = _replace_once(
        data,
        b'''    else
      let ineq_tms1 = map lhand ineq_tms in
      let fun_tms, v1 = exprs_to_vector_fun ineq_tms1 in
''',
        b'''    else
      let _ = candle_nonlinear_profile_marker "verify-call" "problem-reification" "begin" in
      let ineq_tms1 = map lhand ineq_tms in
      let fun_tms, v1 = exprs_to_vector_fun ineq_tms1 in
''',
        "problem-reification-begin",
    )
    data = _replace_once(
        data,
        b'''      let params = ref {params0 with 
			  mono_pass_flag = false;
			  convex_flag = false;
			  allow_derivatives = false} in

      let eval_fs_list, ti_list = unzip (map (mk_verification_functions params pp) fun_tms) in
''',
        b'''      let params = ref {params0 with 
			  mono_pass_flag = false;
			  convex_flag = false;
			  allow_derivatives = false} in
      let _ = candle_nonlinear_profile_marker "verify-call" "problem-reification" "end" in

      let _ = candle_nonlinear_profile_marker "verify-call" "evaluator-build" "begin" in
      let eval_fs_list, ti_list = unzip (map (mk_verification_functions params pp) fun_tms) in
      let _ = candle_nonlinear_profile_marker "verify-call" "evaluator-build" "end" in
''',
        "problem-reification-end-evaluator-build",
    )
    data = _replace_once(
        data,
        b'''      let fs_inf = map (fun f -> f.Informal_verifier.f, f.Informal_verifier.taylor) ti_list in
      let dom_inf = Informal_taylor.mk_m_center_domain pp xx2 zz2 in
      let certificate = Informal_search.construct_certificate opt0 dom_inf fs_inf in

      let stats = Certificate.result_stats certificate in
''',
        b'''      let fs_inf = map (fun f -> f.Informal_verifier.f, f.Informal_verifier.taylor) ti_list in
      let dom_inf = Informal_taylor.mk_m_center_domain pp xx2 zz2 in
      let _ = candle_nonlinear_profile_marker "verify-call" "informal-search" "begin" in
      let certificate = Informal_search.construct_certificate opt0 dom_inf fs_inf in
      let _ = candle_nonlinear_profile_marker "verify-call" "informal-search" "end" in

      let stats = Certificate.result_stats certificate in
''',
        "informal-search",
    )
    data = _replace_once(
        data,
        b'''	  let c1p, _ = Informal_verifier.m_verify_raw0 pp 1 pp ti_list c1 xx2 zz2 in
	  let _ = !info_print_level < 1 || (report0 " done\\n"; true) in

	  let _ = !info_print_level < 1 || (report0 "Formal verification... "; true) in
	  let start = Unix.gettimeofday() in
	  let result = m_p_verify_disj_raw0 n pp eval_fs_list c1p xx1 zz1 in
	  let finish = Unix.gettimeofday() in
''',
        b'''	  let _ = candle_nonlinear_profile_marker "verify-call" "adaptive-informal-verification" "begin" in
	  let c1p, _ = Informal_verifier.m_verify_raw0 pp 1 pp ti_list c1 xx2 zz2 in
	  let _ = candle_nonlinear_profile_marker "verify-call" "adaptive-informal-verification" "end" in
	  let _ = !info_print_level < 1 || (report0 " done\\n"; true) in

	  let _ = !info_print_level < 1 || (report0 "Formal verification... "; true) in
	  let _ = candle_nonlinear_profile_marker "verify-call" "formal-verification" "begin" in
	  let start = Unix.gettimeofday() in
	  let result = m_p_verify_disj_raw0 n pp eval_fs_list c1p xx1 zz1 in
	  let finish = Unix.gettimeofday() in
	  let _ = candle_nonlinear_profile_marker "verify-call" "formal-verification" "end" in
''',
        "adaptive-and-formal-verification",
    )
    data = _replace_once(
        data,
        b'''	  let _ = !info_print_level < 1 || (report0 "Formal verification... "; true) in
	  let start = Unix.gettimeofday() in
	  let result = m_verify_disj_raw0 n pp eval_fs_list c1 xx1 zz1 in
	  let finish = Unix.gettimeofday() in
''',
        b'''	  let _ = !info_print_level < 1 || (report0 "Formal verification... "; true) in
	  let _ = candle_nonlinear_profile_marker "verify-call" "formal-verification" "begin" in
	  let start = Unix.gettimeofday() in
	  let result = m_verify_disj_raw0 n pp eval_fs_list c1 xx1 zz1 in
	  let finish = Unix.gettimeofday() in
	  let _ = candle_nonlinear_profile_marker "verify-call" "formal-verification" "end" in
''',
        "fixed-formal-verification",
    )
    data = _replace_once(
        data,
        b'''	    start, finish, result in
	normalize_disj_result norm_flag fun_tms v1 imp_th1 domain_sub_th result,
  {total_time = finish -. total_start; formal_verification_time = finish -. start; certificate = stats};;
''',
        b'''	    start, finish, result in
	let _ = candle_nonlinear_profile_marker "verify-call" "final-normalization" "begin" in
	let final_result =
	  normalize_disj_result norm_flag fun_tms v1 imp_th1 domain_sub_th result in
	let _ = candle_nonlinear_profile_marker "verify-call" "final-normalization" "end" in
	final_result,
  {total_time = finish -. total_start; formal_verification_time = finish -. start; certificate = stats};;
''',
        "final-normalization",
    )

    digest = hashlib.sha256(data).hexdigest()
    md5 = hashlib.md5(data, usedforsecurity=False).hexdigest()
    prior = record["normalization"]
    record["normalized_bytes"] = data
    record["normalization"] = {
        "authority": "development-only-nonlinear-profile",
        "id": NORMALIZATION_ID,
        "semantic_rule": (
            "insert flushed phase markers around unchanged expressions in the "
            "authenticated disjunctive nonlinear verifier; marker results are "
            "discarded and do not construct or authorize a theorem"
        ),
        "input_normalization": prior,
        "operation_count": 8,
        "normalized_bytes": len(data),
        "normalized_md5": md5,
        "normalized_sha256": digest,
    }
    return {
        "source_key": SOURCE_KEY,
        "input_sha256": INPUT_SHA256,
        "normalized_bytes": len(data),
        "normalized_md5": md5,
        "normalized_sha256": digest,
    }
