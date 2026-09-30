(* Checkpointable reflected proof state for the 860-leaf case16594 plan. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_leaf_grouping.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_family_engine.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_family_prove = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;
open Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;

let candle_disjunctive_case16594_engine_leaves =
  map
    (fun leaf ->
      leaf.case16594_leaf_function_index,leaf.case16594_leaf_domain)
    candle_disjunctive_case16594_leaves;;

let candle_disjunctive_case16594_engine_state =
  candle_disjunctive_family_engine_make
    "case16594" 860 1
    (List.nth candle_disjunctive_case16594_plan_prepared 1)
    candle_disjunctive_case16594_engine_leaves;;

let candle_disjunctive_case16594_prove_next count =
  candle_disjunctive_family_engine_prove_next
    candle_disjunctive_case16594_engine_state count;;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-family" ^
       " scope=proof leaf=" ^
       string_of_int
         !(candle_disjunctive_case16594_engine_state.
           family_engine_next_index) ^
       " phase=" ^ event));;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_FAMILY_SUPPORT_OK next=0/860 DEVELOPMENT_NON_RELEASE";;

end;;
