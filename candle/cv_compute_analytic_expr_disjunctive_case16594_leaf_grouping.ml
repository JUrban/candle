(* Exact precision leaves for disjunctive family member 16594. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16594_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_case16594_leaf_grouping = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_case16594_plan;;

type candle_disjunctive_case16594_leaf = {
  case16594_leaf_function_index : int;
  case16594_leaf_domain : thm;
};;

let candle_disjunctive_case16594_root_domain =
  M_taylor.mk_m_center_domain 6 6
    candle_disjunctive_case16594_plan_xx1
    candle_disjunctive_case16594_plan_zz1;;

let rec candle_disjunctive_case16594_collect domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if raw_flag || function_index < 0 || function_index > 1 then
        failwith "case16594 leaf grouping: unexpected pass selection";
      [{case16594_leaf_function_index = function_index;
        case16594_leaf_domain = domain}]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16594 leaf grouping: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      candle_disjunctive_case16594_collect left_domain left @
      candle_disjunctive_case16594_collect right_domain right
  | P_result_mono _ ->
      failwith "case16594 leaf grouping: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "case16594 leaf grouping: unexpected reference node";;

let candle_disjunctive_case16594_leaves =
  candle_disjunctive_case16594_collect
    candle_disjunctive_case16594_root_domain
    candle_disjunctive_case16594_plan_precision_tree;;

let candle_disjunctive_case16594_function0 =
  length
    (filter
      (fun leaf -> leaf.case16594_leaf_function_index = 0)
      candle_disjunctive_case16594_leaves);;
let candle_disjunctive_case16594_function1 =
  length
    (filter
      (fun leaf -> leaf.case16594_leaf_function_index = 1)
      candle_disjunctive_case16594_leaves);;

if length candle_disjunctive_case16594_leaves <> 860 ||
   candle_disjunctive_case16594_function0 <> 0 ||
   candle_disjunctive_case16594_function1 <> 860 then
  failwith "case16594 leaf grouping: leaf identity drift";;

print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_LEAF_GROUPING_OK leaves=860 function0=0 function1=860 DEVELOPMENT_NON_RELEASE";;

end;;
