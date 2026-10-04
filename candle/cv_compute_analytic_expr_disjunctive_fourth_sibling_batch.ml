(* Three authentic same-expression production-sibling plan probes. *)

needs "candle/cv_compute_analytic_expr_disjunctive_next_sibling_batch.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch;;

let candle_disjunctive_case16364_target,
    candle_disjunctive_case16364_reconstruction,
    candle_disjunctive_case16364_expansion,
    candle_disjunctive_case16364_converted,
    candle_disjunctive_case16364_standard,
    candle_disjunctive_case16364_functions,
    candle_disjunctive_case16364_variable_vector,
    candle_disjunctive_case16364_domain_subset,
    candle_disjunctive_case16364_xx1,
    candle_disjunctive_case16364_zz1,
    candle_disjunctive_case16364_precision_tree,
    candle_disjunctive_case16364_root_domain,
    candle_disjunctive_case16364_leaves,
    candle_disjunctive_case16364_leaf_count,
    candle_disjunctive_case16364_glue_count,
    candle_disjunctive_case16364_function0_count,
    candle_disjunctive_case16364_function1_count =
  candle_disjunctive_next_batch_prepare 34;;

let candle_disjunctive_case16625_target,
    candle_disjunctive_case16625_reconstruction,
    candle_disjunctive_case16625_expansion,
    candle_disjunctive_case16625_converted,
    candle_disjunctive_case16625_standard,
    candle_disjunctive_case16625_functions,
    candle_disjunctive_case16625_variable_vector,
    candle_disjunctive_case16625_domain_subset,
    candle_disjunctive_case16625_xx1,
    candle_disjunctive_case16625_zz1,
    candle_disjunctive_case16625_precision_tree,
    candle_disjunctive_case16625_root_domain,
    candle_disjunctive_case16625_leaves,
    candle_disjunctive_case16625_leaf_count,
    candle_disjunctive_case16625_glue_count,
    candle_disjunctive_case16625_function0_count,
    candle_disjunctive_case16625_function1_count =
  candle_disjunctive_next_batch_prepare 295;;

let candle_disjunctive_case16587_target,
    candle_disjunctive_case16587_reconstruction,
    candle_disjunctive_case16587_expansion,
    candle_disjunctive_case16587_converted,
    candle_disjunctive_case16587_standard,
    candle_disjunctive_case16587_functions,
    candle_disjunctive_case16587_variable_vector,
    candle_disjunctive_case16587_domain_subset,
    candle_disjunctive_case16587_xx1,
    candle_disjunctive_case16587_zz1,
    candle_disjunctive_case16587_precision_tree,
    candle_disjunctive_case16587_root_domain,
    candle_disjunctive_case16587_leaves,
    candle_disjunctive_case16587_leaf_count,
    candle_disjunctive_case16587_glue_count,
    candle_disjunctive_case16587_function0_count,
    candle_disjunctive_case16587_function1_count =
  candle_disjunctive_next_batch_prepare 257;;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898 selection=historical-partition-cost-leads" ^
   " record16364_index=34 leaves=" ^
   string_of_int candle_disjunctive_case16364_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16364_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16364_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16364_function1_count ^
   " record16625_index=295 leaves=" ^
   string_of_int candle_disjunctive_case16625_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16625_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16625_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16625_function1_count ^
   " record16587_index=257 leaves=" ^
   string_of_int candle_disjunctive_case16587_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16587_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16587_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16587_function1_count ^
   " reused_formal_functions=2 reused_direct_programs=2");;

end;;
