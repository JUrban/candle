(* ========================================================================== *)
(* Exact adaptive leaves for the retained disjunctive certificate plan.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Every precision leaf is paired with the       *)
(* function selected by the authenticated ordinary verifier plan.            *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_plan;;

type candle_disjunctive_leaf = {
  disjunctive_leaf_function_index : int;
  disjunctive_leaf_domain : thm;
};;

let candle_disjunctive_leaf_grouping_root_domain =
  M_taylor.mk_m_center_domain
    6 6 candle_disjunctive_plan_xx1 candle_disjunctive_plan_zz1;;

let rec candle_disjunctive_leaf_grouping_collect domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if raw_flag || function_index < 0 || function_index > 1 then
        failwith "disjunctive leaf grouping: unexpected pass selection";
      [{disjunctive_leaf_function_index = function_index;
        disjunctive_leaf_domain = domain}]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "disjunctive leaf grouping: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      candle_disjunctive_leaf_grouping_collect left_domain left @
      candle_disjunctive_leaf_grouping_collect right_domain right
  | P_result_mono _ ->
      failwith "disjunctive leaf grouping: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "disjunctive leaf grouping: unexpected reference node";;

let candle_disjunctive_leaf_grouping_leaves =
  candle_disjunctive_leaf_grouping_collect
    candle_disjunctive_leaf_grouping_root_domain
    candle_disjunctive_plan_precision_tree;;

let candle_disjunctive_leaf_grouping_function0 =
  length
    (filter
      (fun leaf -> leaf.disjunctive_leaf_function_index = 0)
      candle_disjunctive_leaf_grouping_leaves);;
let candle_disjunctive_leaf_grouping_function1 =
  length
    (filter
      (fun leaf -> leaf.disjunctive_leaf_function_index = 1)
      candle_disjunctive_leaf_grouping_leaves);;

if length candle_disjunctive_leaf_grouping_leaves <> 788 ||
   candle_disjunctive_leaf_grouping_function0 <> 0 ||
   candle_disjunctive_leaf_grouping_function1 <> 788 then
  failwith "disjunctive leaf grouping: leaf identity drift";;

let candle_disjunctive_leaf_grouping_domains =
  map (fun leaf -> leaf.disjunctive_leaf_domain)
    candle_disjunctive_leaf_grouping_leaves;;

print_endline
  "CANDLE_CV_DISJUNCTIVE_LEAF_GROUPING_OK leaves=788 function0=0 function1=788 DEVELOPMENT_NON_RELEASE";;

end;;
