(* Genuine sixteen-cell discriminator for the one-verdict complete checker. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_complete_prefix16 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

let rec candle_disjunctive_case16594_complete_prefix16_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 complete prefix16: short cell plan"
  | head :: tail ->
      head ::
      candle_disjunctive_case16594_complete_prefix16_take (count - 1) tail;;

let candle_disjunctive_case16594_complete_prefix16_encode_token token =
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
      | _ -> failwith "case16594 complete prefix16: malformed glue token"
    else failwith "case16594 complete prefix16: unknown compact token";;

let rec candle_disjunctive_case16594_complete_prefix16_decode_stack encoded =
  if aconv encoded `Cexp_num 0` then []
  else
    let head,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 complete prefix16 stack" encoded in
    head ::
    candle_disjunctive_case16594_complete_prefix16_decode_stack tail;;

let _ =
  let axioms_before = axioms () in
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE" ^
         " lane=disjunctive-case16594-complete-prefix16" ^
         " phase=" ^ event));
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  let cells =
    candle_disjunctive_case16594_complete_prefix16_take 16
      candle_disjunctive_case16594_variable_raw_plan_cells in
  let segment_items,remaining_tokens =
    candle_disjunctive_case16594_compact_complete_take_token_segment
      16 [] (dest_list (candle_disjunctive_case16594_compact_token_plan ())) in
  let segment =
    mk_list
      (segment_items,
       type_of candle_disjunctive_case16594_compact_token_leaf) in
  let encoded_segment =
    candle_q_dim_stable_program_cval_list
      (map candle_disjunctive_case16594_complete_prefix16_encode_token
        segment_items) in
  let result =
    candle_q_dim_taylor_model_fixed_outer_variable_complete_stack_six
      prepared cells segment encoded_segment in
  let active_roots =
    length
      (candle_disjunctive_case16594_complete_prefix16_decode_stack
        result.variable_complete_encoded_stack_term) in
  let axioms_after = axioms () in
  if length cells <> 16 || length segment_items <= 15 ||
     remaining_tokens = [] ||
     active_roots <> 3 ||
     hyp result.variable_complete_compute_theorem <> [] ||
     hyp result.variable_complete_stack_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case16594 complete prefix16: validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_COMPLETE_PREFIX16_RESULT" ^
     " numerical_cells=16 token_items=" ^
     string_of_int (length segment_items) ^
     " active_roots=" ^ string_of_int active_roots ^ " assumptions=0");
  print_endline
    "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPLETE_PREFIX16_OK DEVELOPMENT_NON_RELEASE";;

end;;
