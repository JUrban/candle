(* Direct production plan for the next-smallest sibling, record 16597. *)

needs "candle/cv_compute_analytic_expr_disjunctive_shared_sibling_prepare.ml";;

module Candle_cv_analytic_expr_disjunctive_case16597_plan = struct

open Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare;;

let candle_disjunctive_case16597_label = "prep-8293089898";;
let candle_disjunctive_case16597_index = 267;;

let candle_disjunctive_case16597_target,
    candle_disjunctive_case16597_reconstruction,
    candle_disjunctive_case16597_expansion,
    candle_disjunctive_case16597_converted,
    candle_disjunctive_case16597_variable_names,
    candle_disjunctive_case16597_bounds,
    candle_disjunctive_case16597_standard,
    candle_disjunctive_case16597_functions,
    candle_disjunctive_case16597_variable_vector =
  candle_disjunctive_shared_fixture
    candle_disjunctive_case16597_label
    candle_disjunctive_case16597_index;;

let candle_disjunctive_case16597_domain_subset,
    candle_disjunctive_case16597_xx1,
    candle_disjunctive_case16597_zz1,
    candle_disjunctive_case16597_certificate,
    candle_disjunctive_case16597_stats,
    candle_disjunctive_case16597_precision_tree =
  candle_disjunctive_shared_plan
    candle_disjunctive_case16597_variable_names
    candle_disjunctive_case16597_bounds
    candle_disjunctive_case16597_functions
    candle_disjunctive_case16597_variable_vector;;

let candle_disjunctive_case16597_function0,
    candle_disjunctive_case16597_function1 =
  candle_disjunctive_shared_count_functions
    candle_disjunctive_case16597_precision_tree;;

if candle_disjunctive_case16597_stats.pass <> 1061 ||
   candle_disjunctive_case16597_stats.pass_raw <> 0 ||
   candle_disjunctive_case16597_stats.pass_mono <> 0 ||
   candle_disjunctive_case16597_stats.mono <> 0 ||
   candle_disjunctive_case16597_stats.glue <> 1060 ||
   candle_disjunctive_case16597_stats.glue_convex <> 0 ||
   candle_disjunctive_case16597_function0 <> 0 ||
   candle_disjunctive_case16597_function1 <> 1061 ||
   hyp candle_disjunctive_case16597_domain_subset <> [] then
  failwith "case16597 direct plan: authenticated state mismatch";;

print_endline
  "CANDLE_CV_CASE16597_DIRECT_PLAN_OK DEVELOPMENT_NON_RELEASE parent=prep-8293089898 index=267 leaves=1061 glues=1060 function0_leaves=0 function1_leaves=1061 reused_formal_functions=2 reused_direct_programs=2";;

end;;
