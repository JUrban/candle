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


MAIN_SOURCE_KEY = "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
MAIN_INPUT_SHA256 = "e1c689bea39ebb4a0161816c59cf469a2f983c5705d1b392b79a555d38247dbb"
FORMAL_SOURCE_KEY = "flyspeck:formal_ineqs/verifier/m_verifier.hl"
FORMAL_INPUT_SHA256 = "3df1c9a04c169ba81252cd1c8f260fc19b45c492635711521a67fa3409d7be56"
NORMALIZATION_ID = "candle-nonlinear-first-leaf-phase-profile-v2"
MARKER_PREFIX = "CANDLE_CERT_PROFILE lane=nonlinear-leaf"


def _replace_once(data: bytes, before: bytes, after: bytes, label: str) -> bytes:
    count = data.count(before)
    if count != 1:
        raise ValueError(
            f"nonlinear profile anchor drift: {label}: expected 1, got {count}"
        )
    return data.replace(before, after, 1)


def _exact_record(
    records: list[dict[str, Any]], source_key: str, input_sha256: str,
) -> dict[str, Any]:
    matches = [record for record in records if record["source_key"] == source_key]
    if len(matches) != 1:
        raise ValueError(
            f"nonlinear profile source identity is absent or duplicated: {source_key}"
        )
    record = matches[0]
    if hashlib.sha256(record["normalized_bytes"]).hexdigest() != input_sha256:
        raise ValueError(
            f"nonlinear profile normalized source identity drift: {source_key}"
        )
    return record


def _finish_record(
    record: dict[str, Any], data: bytes, input_sha256: str,
    operation_count: int, rule: str,
) -> dict[str, Any]:
    digest = hashlib.sha256(data).hexdigest()
    md5 = hashlib.md5(data, usedforsecurity=False).hexdigest()
    prior = record["normalization"]
    record["normalized_bytes"] = data
    record["normalization"] = {
        "authority": "development-only-nonlinear-profile",
        "id": NORMALIZATION_ID,
        "semantic_rule": rule,
        "input_normalization": prior,
        "operation_count": operation_count,
        "normalized_bytes": len(data),
        "normalized_md5": md5,
        "normalized_sha256": digest,
    }
    return {
        "source_key": record["source_key"],
        "input_sha256": input_sha256,
        "normalized_bytes": len(data),
        "normalized_md5": md5,
        "normalized_sha256": digest,
        "operation_count": operation_count,
    }


def instrument_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Instrument exact normalized verifier sources and update their identities."""

    main_record = _exact_record(records, MAIN_SOURCE_KEY, MAIN_INPUT_SHA256)
    formal_record = _exact_record(records, FORMAL_SOURCE_KEY, FORMAL_INPUT_SHA256)
    data = main_record["normalized_bytes"]

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

    main_receipt = _finish_record(
        main_record,
        data,
        MAIN_INPUT_SHA256,
        8,
        "insert flushed phase markers around unchanged expressions in the "
        "authenticated disjunctive nonlinear verifier; marker results are "
        "discarded and do not construct or authorize a theorem",
    )
    data = formal_record["normalized_bytes"]
    formal_marker_definition = b'''open Certificate;;

let candle_nonlinear_profile_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=nonlinear-leaf scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;
'''
    data = _replace_once(
        data,
        b"open Certificate;;\n",
        formal_marker_definition,
        "formal-marker-definition",
    )
    data = _replace_once(
        data,
        b'''let m_p_verify_disj_raw (report_start, total_size) n p_split fs_list certificate domain_th0 th_list =
  let r_size = p_result_size certificate in
  let r_size2 = float_of_int (if total_size > 0 then total_size else (if r_size > 0 then r_size else 1)) in
  let k = ref 0 in
  let kk = ref report_start in
''',
        b'''let m_p_verify_disj_raw (report_start, total_size) n p_split fs_list certificate domain_th0 th_list =
  let r_size = p_result_size certificate in
  let r_size2 = float_of_int (if total_size > 0 then total_size else (if r_size > 0 then r_size else 1)) in
  let k = ref 0 in
  let glue_k = ref 0 in
  let kk = ref report_start in
''',
        "formal-glue-counter",
    )
    data = _replace_once(
        data,
        b'''\t    let fs = List.nth fs_list j in
\t      if f0_flag then
\t\tlet domain, _, _ = (dest_m_cell_domain o concl) domain_th in
\t\tlet xx, zz = dest_pair domain in
\t\t  m_taylor_cell_list_pass0 n (fs.f p_stat.pp xx zz)
\t      else
\t\tlet taylor_th = fs.taylor p_stat.pp p_stat.pp domain_th in
\t\t  m_taylor_cell_list_pass n p_stat.pp taylor_th''' b"  \n",
        b'''\t    let fs = List.nth fs_list j in
\t    let leaf_scope = "formal-leaf-" ^ string_of_int !k in
\t    let _ = candle_nonlinear_profile_marker leaf_scope "leaf-check" "begin" in
\t    let result =
\t      if f0_flag then
\t\tlet domain, _, _ = (dest_m_cell_domain o concl) domain_th in
\t\tlet xx, zz = dest_pair domain in
\t\t  m_taylor_cell_list_pass0 n (fs.f p_stat.pp xx zz)
\t      else
\t\tlet taylor_th = fs.taylor p_stat.pp p_stat.pp domain_th in
\t\t  m_taylor_cell_list_pass n p_stat.pp taylor_th in
\t    let _ = candle_nonlinear_profile_marker leaf_scope "leaf-check" "end" in
\t      result
''',
        "formal-leaf-check",
    )
    data = _replace_once(
        data,
        b'''\t| P_result_glue (p_stat, i, convex_flag, r1, r2) ->
\t    let domain1_th, domain2_th =
\t      if convex_flag then
\t\tlet d1, _ = restrict_domain n (i + 1) true domain_th in
\t\tlet d2, _ = restrict_domain n (i + 1) false domain_th in
\t\t  d1, d2
\t      else
\t\tsplit_domain n p_split (i + 1) domain_th in
\t    let th1 = rec_verify domain1_th r1 in
\t    let th2 = rec_verify domain2_th r2 in
\t      if convex_flag then
\t\tfailwith "convexity: not implemented"
\t      else
\t\tlet th0 = m_glue_cells_list n (i + 1) th1 th2 in
\t\t  merge_m_cell_list_pass n th0
''',
        b'''\t| P_result_glue (p_stat, i, convex_flag, r1, r2) ->
\t    let _ = glue_k := !glue_k + 1 in
\t    let glue_scope = "formal-glue-" ^ string_of_int !glue_k in
\t    let _ = candle_nonlinear_profile_marker glue_scope "domain-split" "begin" in
\t    let domain1_th, domain2_th =
\t      if convex_flag then
\t\tlet d1, _ = restrict_domain n (i + 1) true domain_th in
\t\tlet d2, _ = restrict_domain n (i + 1) false domain_th in
\t\t  d1, d2
\t      else
\t\tsplit_domain n p_split (i + 1) domain_th in
\t    let _ = candle_nonlinear_profile_marker glue_scope "domain-split" "end" in
\t    let th1 = rec_verify domain1_th r1 in
\t    let th2 = rec_verify domain2_th r2 in
\t      if convex_flag then
\t\tfailwith "convexity: not implemented"
\t      else
\t\tlet _ = candle_nonlinear_profile_marker glue_scope "theorem-glue" "begin" in
\t\tlet th0 = m_glue_cells_list n (i + 1) th1 th2 in
\t\tlet result = merge_m_cell_list_pass n th0 in
\t\tlet _ = candle_nonlinear_profile_marker glue_scope "theorem-glue" "end" in
\t\t  result
''',
        "formal-domain-and-glue",
    )
    formal_receipt = _finish_record(
        formal_record,
        data,
        FORMAL_INPUT_SHA256,
        4,
        "insert flushed markers around each unchanged adaptive formal leaf "
        "check, domain split, and theorem glue expression; marker results are "
        "discarded and do not construct or authorize a theorem",
    )
    return {
        "normalization_id": NORMALIZATION_ID,
        "source_count": 2,
        "sources": [main_receipt, formal_receipt],
    }
