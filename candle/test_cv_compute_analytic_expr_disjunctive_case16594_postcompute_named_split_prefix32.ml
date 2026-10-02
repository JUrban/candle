(* Thirty-two genuine cells through raw numerical computation, compact naming,
   and a second raw topology computation.  The named certificate is never
   unfolded by Kernel.compute.  DEVELOPMENT / NON-RELEASE only. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_split_stack_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_postcompute_named_split_prefix32 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_postcompute_named_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_split_stack_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

let rec candle_disjunctive_case16594_postcompute_named_split_prefix32_take
    count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 named split prefix32: short cell plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_postcompute_named_split_prefix32_take
        (count - 1) tail;;

let candle_disjunctive_case16594_postcompute_named_split_prefix32_encode_token
    token =
  if aconv token
       `Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf` then
    `Cexp_num 0`
  else
    let operator,arguments = strip_comb token in
    if aconv operator
         `Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue` then
      match arguments with
      | [axis] ->
          candle_q_dim_stable_program_cval_pair
            (mk_comb (`Cexp_num`,axis)) `Cexp_num 0`
      | _ -> failwith "case16594 named split prefix32: malformed glue token"
    else failwith "case16594 named split prefix32: unknown compact token";;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-postcompute-named-split-prefix32" ^
         " phase=" ^ event));
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_postcompute_named_split_prefix32_take 32
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let segment_items,remaining_tokens =
    candle_disjunctive_case16594_compact_complete_take_token_segment
      32 [] (dest_list (candle_disjunctive_case16594_compact_token_plan ())) in
  let segment =
    mk_list
      (segment_items,
       type_of candle_disjunctive_case16594_compact_token_leaf) in
  let encoded_segment =
    candle_q_dim_stable_program_cval_list
      (map
        candle_disjunctive_case16594_postcompute_named_split_prefix32_encode_token
        segment_items) in
  let named =
    candle_q_dim_taylor_model_fixed_outer_variable_postcompute_named_prove_six
      prepared
      `candle_disjunctive_case16594_postcompute_named_split_prefix32_jobs:cval`
      cells in
  let raw_result = named.variable_postcompute_named_raw_result in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_split_stack_with_encoded_jobs_six
      raw_result named.variable_postcompute_named_compute_encoded_jobs_term
      named.variable_postcompute_named_jobs_definition
      segment encoded_segment in
  let active_roots =
    length (dest_list result.variable_split_logical_stack_term) in
  let axioms_after = axioms () in
  if length cells <> 32 || length segment_items <> 61 ||
     remaining_tokens = [] || active_roots <> 3 ||
     hyp named.variable_postcompute_named_jobs_definition <> [] ||
     hyp raw_result.variable_raw_accept_theorem <> [] ||
     hyp result.variable_split_topology_compute_theorem <> [] ||
     hyp result.variable_split_run_theorem <> [] ||
     hyp result.variable_split_stack_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 named split prefix32: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_POSTCOMPUTE_NAMED_SPLIT_PREFIX32_RESULT" ^
     " numerical_cells=32 token_items=" ^
     string_of_int (length segment_items) ^
     " active_roots=" ^ string_of_int active_roots ^
     " assumptions=0 axiom_growth=0");
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_POSTCOMPUTE_NAMED_SPLIT_PREFIX32_OK DEVELOPMENT_NON_RELEASE";;

end;;
