(* Validate the general forest handoff against the proved singleton case16597. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16597_complete_forest_adapter = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_forest_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_root_prove;;
open Test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete;;

let candle_disjunctive_case16597_forest_axioms_before = axioms ();;
let candle_disjunctive_case16597_forest_adapter =
  candle_q_dim_taylor_model_fixed_outer_variable_complete_handoff_computed_forest_six
    candle_disjunctive_case16597_prepared
    candle_disjunctive_case16597_logical_token_term
    candle_disjunctive_case16597_encoded_tokens
    candle_disjunctive_case16597_encoded_jobs
    candle_disjunctive_case16597_compute
    [candle_disjunctive_case16597_expected_root_boxes];;

let candle_disjunctive_case16597_forest_source =
  match candle_disjunctive_case16597_forest_adapter.
          variable_complete_forest_source_theorems with
  | [theorem] -> theorem
  | _ -> failwith "case16597 forest adapter: non-singleton result";;
let candle_disjunctive_case16597_forest_axioms_after = axioms ();;

if hyp candle_disjunctive_case16597_forest_source <> [] ||
   not
     (aconv (concl candle_disjunctive_case16597_forest_source)
       (concl
         candle_disjunctive_case16597_root.
           variable_complete_root_source_theorem)) ||
   length candle_disjunctive_case16597_forest_axioms_after <>
     length candle_disjunctive_case16597_forest_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_case16597_forest_axioms_before)
       candle_disjunctive_case16597_forest_axioms_after) then
  failwith "case16597 forest adapter: source theorem drift";;

print_endline
  "CANDLE_CV_CASE16597_COMPLETE_FOREST_ADAPTER_OK DEVELOPMENT_NON_RELEASE roots=1 assumptions=0 axiom_growth=0";;

end;;
