(* Genuine first-four-cell compact streaming discriminator for case 16594. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix4 = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

let rec candle_disjunctive_case16594_compact_stream_prefix4_take count =
  function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 compact stream prefix4: short cell plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_compact_stream_prefix4_take
        (count - 1) tail;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-compact-stream-prefix4" ^
         " phase=" ^ event));
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_compact_stream_prefix4_take 4
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let segment_items,remaining_tokens =
    candle_disjunctive_case16594_compact_complete_take_token_segment
      4 [] (dest_list (candle_disjunctive_case16594_compact_token_plan ())) in
  let segment =
    mk_list
      (segment_items,
       type_of candle_disjunctive_case16594_compact_token_leaf) in
  let raw =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
      prepared cells in
  let final_state =
    candle_q_dim_taylor_model_fixed_outer_variable_compact_step_six
      prepared
      (candle_q_dim_taylor_model_fixed_outer_variable_compact_initial_six
        prepared)
      raw.variable_raw_decoded_jobs_term raw.variable_raw_accept_theorem
      segment in
  let active_roots =
    length (dest_list final_state.variable_compact_state_stack_term) in
  let axioms_after = axioms () in
  if length cells <> 4 || segment_items = [] || remaining_tokens = [] ||
     active_roots <= 0 ||
     hyp final_state.variable_compact_state_pass_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 compact stream prefix4: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_PREFIX4_RESULT" ^
     " numerical_cells=4 token_items=" ^ string_of_int (length segment_items) ^
     " active_roots=" ^ string_of_int active_roots ^
     " assumptions=0");
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STREAM_PREFIX4_OK DEVELOPMENT_NON_RELEASE";;

end;;
