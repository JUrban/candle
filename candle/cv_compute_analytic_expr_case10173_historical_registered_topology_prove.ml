(* ========================================================================== *)
(* Logical handoff for the registered case-10173 compact-topology capture.   *)
(*                                                                            *)
(* Numerical acceptance and job representation are deliberately separate.    *)
(* Given the representation theorem exported by the registered ledger, this  *)
(* adapter decodes the closed topology computation into the logical compact   *)
(* run equation consumed by the already-proved original-theorem bridge.       *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_registered_topology_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_topology_capture;;

type candle_case10173_historical_registered_topology_result = {
  registered_topology_root_boxes : term;
  registered_topology_run_theorem : thm;
};;

let candle_case10173_historical_registered_topology_prove
    encoded_jobs jobs_representation captured =
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_REPRESENTATION_BEGIN";
  let decoded_jobs =
    mk_comb (`candle_cv_fso_variable_jobs_decode`,encoded_jobs) in
  let expected_representation =
    mk_eq
      (mk_comb
        (`candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs`,
         decoded_jobs),
       encoded_jobs) in
  if hyp jobs_representation <> [] ||
     not (aconv (concl jobs_representation) expected_representation)
  then failwith "case10173 registered topology prove: representation mismatch";
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_REPRESENTATION_END";
  let tokens = captured.registered_topology_tokens
  and encoded_tokens = captured.registered_topology_encoded_tokens
  and encoded_root = captured.registered_topology_encoded_root
  and reflected_compute = captured.registered_topology_compute_theorem in
  let token_call =
    mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens`,
       tokens) in
  let token_encoding =
    REWRITE_CONV
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def]
      token_call in
  if hyp token_encoding <> [] ||
     not (aconv (rand (concl token_encoding)) encoded_tokens)
  then failwith "case10173 registered topology prove: token encoding mismatch";
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_TOKEN_ENCODING_END";
  let empty_stack =
    `[]:((((num#num)#num)#((num#num)#num))list)list` in
  let empty_jobs =
    `[]:((((num#num)#num)#((num#num)#num))list#
         ((((num#num)#num)#((num#num)#num))list#
          (((num#num)#num)#((num#num)#num))list))list` in
  let stack_encoding =
    REWRITE_CONV [candle_cv_q_boxes_stack_def]
      (mk_comb (`candle_cv_q_boxes_stack`,empty_stack)) in
  let reflected_call =
    list_mk_comb
      (`candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`,
       [`Cexp_num 6`;encoded_tokens;encoded_jobs;`Cexp_num 0`]) in
  if hyp reflected_compute <> [] ||
     not (aconv (lhand (concl reflected_compute)) reflected_call)
  then failwith "case10173 registered topology prove: compute mismatch";
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_COMPUTE_VALIDATION_END";
  let correspondence =
    SPECL
      [tokens;`6`;decoded_jobs;empty_stack]
      candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct in
  let call_encoding =
    candle_q_dim_analytic_jet_congr_apps
      (REFL
        `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run`)
      [REFL `Cexp_num 6`;token_encoding;jobs_representation;stack_encoding] in
  let correspondence_encoded = TRANS (SYM call_encoding) correspondence in
  if not (aconv (lhand (concl correspondence_encoded)) reflected_call) then
    failwith "case10173 registered topology prove: correspondence mismatch";
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_CORRESPONDENCE_END";
  let encoded_logical_result =
    TRANS (SYM correspondence_encoded) reflected_compute in
  let decoded_logical_result =
    AP_TERM
      `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
      encoded_logical_result in
  let decoded_logical_left =
    CONV_RULE
      (LAND_CONV
        (REWR_CONV
          candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip))
      decoded_logical_result in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_LOGICAL_LEFT_END";
  let run_theorem =
    CONV_RULE
      (RAND_CONV
        (REWRITE_CONV
          [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
           CONJUNCT1 candle_cv_fso_variable_jobs_decode_def;
           candle_cv_q_boxes_stack_decode_def;
           cexp_fst_def;cexp_snd_def;injectivity "cval"]))
      decoded_logical_left in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_LOGICAL_RESULT_END";
  let run_left,run_right = dest_eq (concl run_theorem) in
  let success,payload = dest_pair run_right in
  let remaining,stack = dest_pair payload in
  let roots = dest_list stack in
  let root_boxes =
    match roots with
    | [root] -> root
    | _ -> failwith "case10173 registered topology prove: root-count drift" in
  print_endline "CANDLE_REGISTERED_TOPOLOGY_HANDOFF_ROOT_TERM_END";
  let run_operator,run_arguments = strip_comb run_left in
  let run_name,_ = dest_const run_operator in
  let run_shape_matches =
    run_name =
      "candle_q_dim_taylor_model_fixed_outer_variable_compact_run" &&
    length run_arguments = 4 in
  if hyp run_theorem <> [] ||
     not run_shape_matches ||
     not (aconv success `T`) ||
     not (aconv remaining empty_jobs)
  then failwith "case10173 registered topology prove: logical result mismatch";
  {registered_topology_root_boxes = root_boxes;
   registered_topology_run_theorem = run_theorem};;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_TOPOLOGY_PROVE_OK DEVELOPMENT_NON_RELEASE";;

end;;
