(* Three more authentic same-expression production siblings. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;

module Candle_cv_analytic_expr_disjunctive_second_sibling_batch = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;

let candle_disjunctive_case16482_target,
    candle_disjunctive_case16482_reconstruction,
    candle_disjunctive_case16482_expansion,
    candle_disjunctive_case16482_converted,
    candle_disjunctive_case16482_standard,
    candle_disjunctive_case16482_functions,
    candle_disjunctive_case16482_variable_vector,
    candle_disjunctive_case16482_domain_subset,
    candle_disjunctive_case16482_xx1,
    candle_disjunctive_case16482_zz1,
    candle_disjunctive_case16482_precision_tree,
    candle_disjunctive_case16482_root_domain,
    candle_disjunctive_case16482_leaves,
    candle_disjunctive_case16482_leaf_count,
    candle_disjunctive_case16482_glue_count,
    candle_disjunctive_case16482_function0_count,
    candle_disjunctive_case16482_function1_count =
  candle_disjunctive_next_batch_prepare 152;;

let candle_disjunctive_case16656_target,
    candle_disjunctive_case16656_reconstruction,
    candle_disjunctive_case16656_expansion,
    candle_disjunctive_case16656_converted,
    candle_disjunctive_case16656_standard,
    candle_disjunctive_case16656_functions,
    candle_disjunctive_case16656_variable_vector,
    candle_disjunctive_case16656_domain_subset,
    candle_disjunctive_case16656_xx1,
    candle_disjunctive_case16656_zz1,
    candle_disjunctive_case16656_precision_tree,
    candle_disjunctive_case16656_root_domain,
    candle_disjunctive_case16656_leaves,
    candle_disjunctive_case16656_leaf_count,
    candle_disjunctive_case16656_glue_count,
    candle_disjunctive_case16656_function0_count,
    candle_disjunctive_case16656_function1_count =
  candle_disjunctive_next_batch_prepare 326;;

let candle_disjunctive_case16647_target,
    candle_disjunctive_case16647_reconstruction,
    candle_disjunctive_case16647_expansion,
    candle_disjunctive_case16647_converted,
    candle_disjunctive_case16647_standard,
    candle_disjunctive_case16647_functions,
    candle_disjunctive_case16647_variable_vector,
    candle_disjunctive_case16647_domain_subset,
    candle_disjunctive_case16647_xx1,
    candle_disjunctive_case16647_zz1,
    candle_disjunctive_case16647_precision_tree,
    candle_disjunctive_case16647_root_domain,
    candle_disjunctive_case16647_leaves,
    candle_disjunctive_case16647_leaf_count,
    candle_disjunctive_case16647_glue_count,
    candle_disjunctive_case16647_function0_count,
    candle_disjunctive_case16647_function1_count =
  candle_disjunctive_next_batch_prepare 317;;

if candle_disjunctive_case16482_leaf_count <> 1347 ||
   candle_disjunctive_case16656_leaf_count <> 1349 ||
   candle_disjunctive_case16647_leaf_count <> 1369 then
  failwith "second sibling batch: historical leaf-count drift";;

print_endline
  ("CANDLE_CV_SECOND_SIBLING_BATCH_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898" ^
   " record16482_index=152 leaves=" ^
   string_of_int candle_disjunctive_case16482_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16482_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16482_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16482_function1_count ^
   " record16656_index=326 leaves=" ^
   string_of_int candle_disjunctive_case16656_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16656_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16656_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16656_function1_count ^
   " record16647_index=317 leaves=" ^
   string_of_int candle_disjunctive_case16647_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16647_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16647_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16647_function1_count ^
   " reused_formal_functions=2 reused_direct_programs=2");;

end;;
