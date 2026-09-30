(* Reusable accepted eight-cell fixture for compact-stream experiments. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_compact_stack_complete_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_stream_prefix8_fixture = struct

open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_plan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_case16594_compact_token_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_compact_stack_complete_prove;;

let rec candle_disjunctive_case16594_prefix8_fixture_take count = function
  | _ when count = 0 -> []
  | [] -> failwith "case16594 prefix8 fixture: short cell plan"
  | head :: tail ->
      head :: candle_disjunctive_case16594_prefix8_fixture_take (count - 1) tail;;

let candle_disjunctive_case16594_prefix8_fixture_encode_token token =
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
      | _ -> failwith "case16594 prefix8 fixture: malformed glue token"
    else failwith "case16594 prefix8 fixture: unknown compact token";;

let candle_disjunctive_case16594_prefix8_fixture_axioms_before = axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE" ^
       " lane=disjunctive-case16594-prefix8-fixture" ^
       " phase=" ^ event));;

let candle_disjunctive_case16594_prefix8_fixture_prepared =
  candle_disjunctive_case16594_engine_state.family_engine_prepared;;

let candle_disjunctive_case16594_prefix8_fixture_cells =
  candle_disjunctive_case16594_prefix8_fixture_take 8
    candle_disjunctive_case16594_variable_raw_plan_cells;;

let candle_disjunctive_case16594_prefix8_fixture_segment_items,
    candle_disjunctive_case16594_prefix8_fixture_remaining_tokens =
  candle_disjunctive_case16594_compact_complete_take_token_segment
    8 [] (dest_list (candle_disjunctive_case16594_compact_token_plan ()));;

let candle_disjunctive_case16594_prefix8_fixture_segment =
  mk_list
    (candle_disjunctive_case16594_prefix8_fixture_segment_items,
     type_of candle_disjunctive_case16594_compact_token_leaf);;

let candle_disjunctive_case16594_prefix8_fixture_encoded_segment =
  candle_q_dim_stable_program_cval_list
    (map candle_disjunctive_case16594_prefix8_fixture_encode_token
      candle_disjunctive_case16594_prefix8_fixture_segment_items);;

let candle_disjunctive_case16594_prefix8_fixture_raw =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
    candle_disjunctive_case16594_prefix8_fixture_prepared
    candle_disjunctive_case16594_prefix8_fixture_cells;;

let candle_disjunctive_case16594_prefix8_fixture_axioms_after = axioms ();;

if length candle_disjunctive_case16594_prefix8_fixture_cells <> 8 ||
   candle_disjunctive_case16594_prefix8_fixture_segment_items = [] ||
   candle_disjunctive_case16594_prefix8_fixture_remaining_tokens = [] ||
   hyp candle_disjunctive_case16594_prefix8_fixture_raw.
     variable_raw_accept_theorem <> [] ||
   length candle_disjunctive_case16594_prefix8_fixture_axioms_after <>
     length candle_disjunctive_case16594_prefix8_fixture_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom
           candle_disjunctive_case16594_prefix8_fixture_axioms_before)
       candle_disjunctive_case16594_prefix8_fixture_axioms_after) then
  failwith "case16594 prefix8 fixture: validation failed";;

print_endline
  ("CANDLE_CV_DISJUNCTIVE_CASE16594_PREFIX8_FIXTURE_OK cells=8 token_items=" ^
   string_of_int
     (length candle_disjunctive_case16594_prefix8_fixture_segment_items) ^
   " assumptions=0 DEVELOPMENT_NON_RELEASE");;

end;;
