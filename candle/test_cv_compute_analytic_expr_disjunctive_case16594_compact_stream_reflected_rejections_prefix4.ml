(* Fail-closed checks for the reflected compact topology stream. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_reflected_rejections_prefix4 = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4_fixture;;

let rec candle_reflected_compact_dest_cval_list context encoded =
  if aconv encoded `Cexp_num 0` then []
  else
    let head,tail =
      candle_q_dim_stable_program_dest_cval_pair context encoded in
    head :: candle_reflected_compact_dest_cval_list context tail;;

let candle_reflected_compact_is_pair value =
  let operator,arguments = strip_comb value in
  aconv operator `Cexp_pair` && length arguments = 2;;

let rec candle_reflected_compact_first_pair = function
  | [] -> failwith "reflected compact rejections: no glue token"
  | head :: tail ->
      if candle_reflected_compact_is_pair head then head
      else candle_reflected_compact_first_pair tail;;

let rec candle_reflected_compact_replace_first_pair replacement = function
  | [] -> failwith "reflected compact rejections: no glue token"
  | head :: tail ->
      if candle_reflected_compact_is_pair head then replacement head :: tail
      else head :: candle_reflected_compact_replace_first_pair replacement tail;;

let candle_reflected_compact_compute encoded_tokens encoded_jobs =
  Kernel.compute
    (COMPUTE_INIT_THMS,
     candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs)
    (list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;encoded_jobs;`Cexp_num 0`]));;

let candle_reflected_compact_result theorem =
  let success,payload =
    candle_q_dim_stable_program_dest_cval_pair
      "reflected compact rejection result" (rand (concl theorem)) in
  let remaining,stack =
    candle_q_dim_stable_program_dest_cval_pair
      "reflected compact rejection payload" payload in
  success,remaining,stack;;

let candle_reflected_compact_expect_rejection name theorem =
  let success,_,_ = candle_reflected_compact_result theorem in
  if hyp theorem <> [] || not (aconv success `Cexp_num 0`) then
    failwith ("reflected compact rejections: accepted " ^ name);;

let _ =
  let encoded_tokens =
    candle_disjunctive_case16594_prefix4_fixture_encoded_segment in
  let encoded_jobs =
    candle_disjunctive_case16594_prefix4_fixture_raw.
      variable_raw_encoded_jobs_term in
  let token_items =
    candle_reflected_compact_dest_cval_list "reflected compact tokens"
      encoded_tokens in
  let job_items =
    candle_reflected_compact_dest_cval_list "reflected compact jobs"
      encoded_jobs in
  let first_glue = candle_reflected_compact_first_pair token_items in
  let malformed_leaf =
    match token_items with
    | [] -> failwith "reflected compact rejections: empty token stream"
    | _ :: tail -> `Cexp_num 2` :: tail in
  let malformed_marker =
    candle_reflected_compact_replace_first_pair
      (fun glue ->
        let axis,_ =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact glue" glue in
        candle_q_dim_stable_program_cval_pair axis `Cexp_num 1`)
      token_items in
  let out_of_range_axis =
    candle_reflected_compact_replace_first_pair
      (fun _ ->
        candle_q_dim_stable_program_cval_pair `Cexp_num 7` `Cexp_num 0`)
      token_items in
  let wrong_valid_axis =
    candle_reflected_compact_replace_first_pair
      (fun glue ->
        let axis,_ =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact glue" glue in
        let replacement =
          if aconv axis `Cexp_num 1` then `Cexp_num 2` else `Cexp_num 1` in
        candle_q_dim_stable_program_cval_pair replacement `Cexp_num 0`)
      token_items in
  let bad_split_jobs =
    match job_items with
    | first :: second :: remaining ->
        let _,first_payload =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact first job" first in
        let _,first_boxes =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact first job payload" first_payload in
        let second_whole,second_payload =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact second job" second in
        let second_center,_ =
          candle_q_dim_stable_program_dest_cval_pair
            "reflected compact second job payload" second_payload in
        let changed_second =
          candle_q_dim_stable_program_cval_pair second_whole
            (candle_q_dim_stable_program_cval_pair second_center first_boxes) in
        first :: changed_second :: remaining
    | _ -> failwith "reflected compact rejections: short job stream" in
  let reject name tokens jobs =
    candle_reflected_compact_expect_rejection name
      (candle_reflected_compact_compute
        (candle_q_dim_stable_program_cval_list tokens)
        (candle_q_dim_stable_program_cval_list jobs)) in
  reject "malformed leaf tag" malformed_leaf job_items;
  reject "malformed glue marker" malformed_marker job_items;
  reject "out-of-range axis" out_of_range_axis job_items;
  reject "wrong valid split axis" wrong_valid_axis job_items;
  reject "missing branch" [first_glue] job_items;
  reject "changed split boxes" token_items bad_split_jobs;
  let leftover = candle_reflected_compact_compute `Cexp_num 0` encoded_jobs in
  let leftover_success,leftover_jobs,leftover_stack =
    candle_reflected_compact_result leftover in
  if hyp leftover <> [] ||
     not (aconv leftover_success `Cexp_num 1`) ||
     not (aconv leftover_jobs encoded_jobs) ||
     not (aconv leftover_stack `Cexp_num 0`) then
    failwith "reflected compact rejections: leftover-jobs boundary mismatch";
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_REFLECTED_REJECTIONS_PREFIX4_OK malformed_leaf=true malformed_glue=true bad_axis=true wrong_axis=true missing_branch=true changed_split=true leftover_jobs_detected=true DEVELOPMENT_NON_RELEASE";;

end;;
