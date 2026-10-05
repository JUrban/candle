(* Three more authentic same-expression production siblings.                 *)
(*                                                                           *)
(* The pinned Flyspeck Azure pass counts are used only to prioritize a small *)
(* batch.  Candle independently reconstructs each plan below and fails closed *)
(* if its resulting leaf count does not match the historical lead.           *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;

let candle_disjunctive_case16646_target,
    candle_disjunctive_case16646_reconstruction,
    candle_disjunctive_case16646_expansion,
    candle_disjunctive_case16646_converted,
    candle_disjunctive_case16646_standard,
    candle_disjunctive_case16646_functions,
    candle_disjunctive_case16646_variable_vector,
    candle_disjunctive_case16646_domain_subset,
    candle_disjunctive_case16646_xx1,
    candle_disjunctive_case16646_zz1,
    candle_disjunctive_case16646_precision_tree,
    candle_disjunctive_case16646_root_domain,
    candle_disjunctive_case16646_leaves,
    candle_disjunctive_case16646_leaf_count,
    candle_disjunctive_case16646_glue_count,
    candle_disjunctive_case16646_function0_count,
    candle_disjunctive_case16646_function1_count =
  candle_disjunctive_next_batch_prepare 316;;

let candle_disjunctive_case16659_target,
    candle_disjunctive_case16659_reconstruction,
    candle_disjunctive_case16659_expansion,
    candle_disjunctive_case16659_converted,
    candle_disjunctive_case16659_standard,
    candle_disjunctive_case16659_functions,
    candle_disjunctive_case16659_variable_vector,
    candle_disjunctive_case16659_domain_subset,
    candle_disjunctive_case16659_xx1,
    candle_disjunctive_case16659_zz1,
    candle_disjunctive_case16659_precision_tree,
    candle_disjunctive_case16659_root_domain,
    candle_disjunctive_case16659_leaves,
    candle_disjunctive_case16659_leaf_count,
    candle_disjunctive_case16659_glue_count,
    candle_disjunctive_case16659_function0_count,
    candle_disjunctive_case16659_function1_count =
  candle_disjunctive_next_batch_prepare 329;;

let candle_disjunctive_case16658_target,
    candle_disjunctive_case16658_reconstruction,
    candle_disjunctive_case16658_expansion,
    candle_disjunctive_case16658_converted,
    candle_disjunctive_case16658_standard,
    candle_disjunctive_case16658_functions,
    candle_disjunctive_case16658_variable_vector,
    candle_disjunctive_case16658_domain_subset,
    candle_disjunctive_case16658_xx1,
    candle_disjunctive_case16658_zz1,
    candle_disjunctive_case16658_precision_tree,
    candle_disjunctive_case16658_root_domain,
    candle_disjunctive_case16658_leaves,
    candle_disjunctive_case16658_leaf_count,
    candle_disjunctive_case16658_glue_count,
    candle_disjunctive_case16658_function0_count,
    candle_disjunctive_case16658_function1_count =
  candle_disjunctive_next_batch_prepare 328;;

if candle_disjunctive_case16646_leaf_count <> 1710 ||
   candle_disjunctive_case16659_leaf_count <> 1751 ||
   candle_disjunctive_case16658_leaf_count <> 2278 then
  failwith "fifth sibling batch: pinned historical leaf-count drift";;

if candle_disjunctive_case16646_leaf_count +
   candle_disjunctive_case16659_leaf_count +
   candle_disjunctive_case16658_leaf_count <> 5739 then
  failwith "fifth sibling batch: total leaf-count drift";;

print_endline
  ("CANDLE_CV_FIFTH_SIBLING_BATCH_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898" ^
   " selection=pinned-azure-pass-count-ranked-lead-only" ^
   " record16646_index=316 leaves=" ^
   string_of_int candle_disjunctive_case16646_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16646_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16646_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16646_function1_count ^
   " record16659_index=329 leaves=" ^
   string_of_int candle_disjunctive_case16659_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16659_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16659_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16659_function1_count ^
   " record16658_index=328 leaves=" ^
   string_of_int candle_disjunctive_case16658_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16658_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16658_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16658_function1_count ^
   " total_leaves=5739" ^
   " reused_formal_functions=2 reused_direct_programs=2");;

end;;
