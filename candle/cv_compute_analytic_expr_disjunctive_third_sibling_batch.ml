(* Three further authentic same-expression production siblings. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;

module Candle_cv_analytic_expr_disjunctive_third_sibling_batch = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;

let candle_disjunctive_case16480_target,
    candle_disjunctive_case16480_reconstruction,
    candle_disjunctive_case16480_expansion,
    candle_disjunctive_case16480_converted,
    candle_disjunctive_case16480_standard,
    candle_disjunctive_case16480_functions,
    candle_disjunctive_case16480_variable_vector,
    candle_disjunctive_case16480_domain_subset,
    candle_disjunctive_case16480_xx1,
    candle_disjunctive_case16480_zz1,
    candle_disjunctive_case16480_precision_tree,
    candle_disjunctive_case16480_root_domain,
    candle_disjunctive_case16480_leaves,
    candle_disjunctive_case16480_leaf_count,
    candle_disjunctive_case16480_glue_count,
    candle_disjunctive_case16480_function0_count,
    candle_disjunctive_case16480_function1_count =
  candle_disjunctive_next_batch_prepare 150;;

let candle_disjunctive_case16339_target,
    candle_disjunctive_case16339_reconstruction,
    candle_disjunctive_case16339_expansion,
    candle_disjunctive_case16339_converted,
    candle_disjunctive_case16339_standard,
    candle_disjunctive_case16339_functions,
    candle_disjunctive_case16339_variable_vector,
    candle_disjunctive_case16339_domain_subset,
    candle_disjunctive_case16339_xx1,
    candle_disjunctive_case16339_zz1,
    candle_disjunctive_case16339_precision_tree,
    candle_disjunctive_case16339_root_domain,
    candle_disjunctive_case16339_leaves,
    candle_disjunctive_case16339_leaf_count,
    candle_disjunctive_case16339_glue_count,
    candle_disjunctive_case16339_function0_count,
    candle_disjunctive_case16339_function1_count =
  candle_disjunctive_next_batch_prepare 9;;

let candle_disjunctive_case16595_target,
    candle_disjunctive_case16595_reconstruction,
    candle_disjunctive_case16595_expansion,
    candle_disjunctive_case16595_converted,
    candle_disjunctive_case16595_standard,
    candle_disjunctive_case16595_functions,
    candle_disjunctive_case16595_variable_vector,
    candle_disjunctive_case16595_domain_subset,
    candle_disjunctive_case16595_xx1,
    candle_disjunctive_case16595_zz1,
    candle_disjunctive_case16595_precision_tree,
    candle_disjunctive_case16595_root_domain,
    candle_disjunctive_case16595_leaves,
    candle_disjunctive_case16595_leaf_count,
    candle_disjunctive_case16595_glue_count,
    candle_disjunctive_case16595_function0_count,
    candle_disjunctive_case16595_function1_count =
  candle_disjunctive_next_batch_prepare 265;;

if candle_disjunctive_case16480_leaf_count <> 1458 ||
   candle_disjunctive_case16339_leaf_count <> 1519 ||
   candle_disjunctive_case16595_leaf_count <> 1638 then
  failwith "third sibling batch: historical leaf-count drift";;

print_endline
  ("CANDLE_CV_THIRD_SIBLING_BATCH_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898" ^
   " record16480_index=150 leaves=" ^
   string_of_int candle_disjunctive_case16480_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16480_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16480_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16480_function1_count ^
   " record16339_index=9 leaves=" ^
   string_of_int candle_disjunctive_case16339_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16339_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16339_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16339_function1_count ^
   " record16595_index=265 leaves=" ^
   string_of_int candle_disjunctive_case16595_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16595_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16595_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16595_function1_count ^
   " reused_formal_functions=2 reused_direct_programs=2");;

end;;
