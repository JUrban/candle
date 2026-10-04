(* ========================================================================== *)
(* Three authentic same-expression production siblings prepared as a batch. *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_shared_sibling_prepare.ml";;

module Candle_cv_analytic_expr_disjunctive_next_sibling_batch = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_shared_sibling_prepare;;

let candle_disjunctive_next_batch_label = "prep-8293089898";;

let rec candle_disjunctive_next_batch_collect domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index < 0 || function_index > 1 || raw_flag then
        failwith "next sibling batch: pass selection drift";
      [function_index,domain]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "next sibling batch: convex node";
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      candle_disjunctive_next_batch_collect left_domain left @
      candle_disjunctive_next_batch_collect right_domain right
  | P_result_mono _ ->
      failwith "next sibling batch: monotonicity node"
  | P_result_ref _ ->
      failwith "next sibling batch: reference node";;

let candle_disjunctive_next_batch_prepare index =
  let target,reconstruction,expansion,converted,variable_names,bounds,
      standard,functions,variable_vector =
    candle_disjunctive_shared_fixture
      candle_disjunctive_next_batch_label index in
  let domain_subset,xx1,zz1,_certificate,stats,precision_tree =
    candle_disjunctive_shared_plan
      variable_names bounds functions variable_vector in
  let function0,function1 =
    candle_disjunctive_shared_count_functions precision_tree in
  let root_domain = M_taylor.mk_m_center_domain 6 6 xx1 zz1 in
  let leaves =
    candle_disjunctive_next_batch_collect root_domain precision_tree in
  if stats.pass <= 0 ||
     stats.pass_raw <> 0 ||
     stats.pass_mono <> 0 ||
     stats.mono <> 0 ||
     stats.glue <> stats.pass - 1 ||
     stats.glue_convex <> 0 ||
     function0 + function1 <> stats.pass ||
     length leaves <> stats.pass ||
     hyp domain_subset <> [] ||
     not (List.for_all (fun (_,domain) -> hyp domain = []) leaves) then
    failwith "next sibling batch: authenticated plan mismatch";
  target,reconstruction,expansion,converted,standard,functions,
  variable_vector,domain_subset,xx1,zz1,precision_tree,root_domain,leaves,
  stats.pass,stats.glue,function0,function1;;

let candle_disjunctive_case16617_target,
    candle_disjunctive_case16617_reconstruction,
    candle_disjunctive_case16617_expansion,
    candle_disjunctive_case16617_converted,
    candle_disjunctive_case16617_standard,
    candle_disjunctive_case16617_functions,
    candle_disjunctive_case16617_variable_vector,
    candle_disjunctive_case16617_domain_subset,
    candle_disjunctive_case16617_xx1,
    candle_disjunctive_case16617_zz1,
    candle_disjunctive_case16617_precision_tree,
    candle_disjunctive_case16617_root_domain,
    candle_disjunctive_case16617_leaves,
    candle_disjunctive_case16617_leaf_count,
    candle_disjunctive_case16617_glue_count,
    candle_disjunctive_case16617_function0_count,
    candle_disjunctive_case16617_function1_count =
  candle_disjunctive_next_batch_prepare 287;;

let candle_disjunctive_case16593_target,
    candle_disjunctive_case16593_reconstruction,
    candle_disjunctive_case16593_expansion,
    candle_disjunctive_case16593_converted,
    candle_disjunctive_case16593_standard,
    candle_disjunctive_case16593_functions,
    candle_disjunctive_case16593_variable_vector,
    candle_disjunctive_case16593_domain_subset,
    candle_disjunctive_case16593_xx1,
    candle_disjunctive_case16593_zz1,
    candle_disjunctive_case16593_precision_tree,
    candle_disjunctive_case16593_root_domain,
    candle_disjunctive_case16593_leaves,
    candle_disjunctive_case16593_leaf_count,
    candle_disjunctive_case16593_glue_count,
    candle_disjunctive_case16593_function0_count,
    candle_disjunctive_case16593_function1_count =
  candle_disjunctive_next_batch_prepare 263;;

let candle_disjunctive_case16582_target,
    candle_disjunctive_case16582_reconstruction,
    candle_disjunctive_case16582_expansion,
    candle_disjunctive_case16582_converted,
    candle_disjunctive_case16582_standard,
    candle_disjunctive_case16582_functions,
    candle_disjunctive_case16582_variable_vector,
    candle_disjunctive_case16582_domain_subset,
    candle_disjunctive_case16582_xx1,
    candle_disjunctive_case16582_zz1,
    candle_disjunctive_case16582_precision_tree,
    candle_disjunctive_case16582_root_domain,
    candle_disjunctive_case16582_leaves,
    candle_disjunctive_case16582_leaf_count,
    candle_disjunctive_case16582_glue_count,
    candle_disjunctive_case16582_function0_count,
    candle_disjunctive_case16582_function1_count =
  candle_disjunctive_next_batch_prepare 252;;

print_endline
  ("CANDLE_CV_NEXT_SIBLING_BATCH_PLAN_OK DEVELOPMENT_NON_RELEASE" ^
   " parent=prep-8293089898" ^
   " record16617_index=287 leaves=" ^
   string_of_int candle_disjunctive_case16617_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16617_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16617_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16617_function1_count ^
   " record16593_index=263 leaves=" ^
   string_of_int candle_disjunctive_case16593_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16593_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16593_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16593_function1_count ^
   " record16582_index=252 leaves=" ^
   string_of_int candle_disjunctive_case16582_leaf_count ^
   " glues=" ^ string_of_int candle_disjunctive_case16582_glue_count ^
   " function0=" ^
   string_of_int candle_disjunctive_case16582_function0_count ^
   " function1=" ^
   string_of_int candle_disjunctive_case16582_function1_count ^
   " reused_formal_functions=2" ^
   " reused_direct_programs=2");;

end;;
