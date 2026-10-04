(* Exact adaptive domains for direct production sibling 267. *)

needs "candle/cv_compute_analytic_expr_disjunctive_case16597_direct_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_case16597_leaf_grouping = struct

open Certificate;;
open Candle_cv_analytic_expr_disjunctive_case16597_plan;;

let candle_disjunctive_case16597_root_domain =
  M_taylor.mk_m_center_domain 6 6
    candle_disjunctive_case16597_xx1
    candle_disjunctive_case16597_zz1;;

let rec candle_disjunctive_case16597_collect domain tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 1 || raw_flag then
        failwith "case16597 direct grouping: pass selection drift";
      [domain]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "case16597 direct grouping: convex node";
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 (split_index + 1) domain in
      candle_disjunctive_case16597_collect left_domain left @
      candle_disjunctive_case16597_collect right_domain right
  | P_result_mono _ ->
      failwith "case16597 direct grouping: monotonicity node"
  | P_result_ref _ ->
      failwith "case16597 direct grouping: reference node";;

let candle_disjunctive_case16597_leaves =
  candle_disjunctive_case16597_collect
    candle_disjunctive_case16597_root_domain
    candle_disjunctive_case16597_precision_tree;;

if length candle_disjunctive_case16597_leaves <> 1061 ||
   not
     (List.for_all (fun domain -> hyp domain = [])
       candle_disjunctive_case16597_leaves) then
  failwith "case16597 direct grouping: leaf identity drift";;

print_endline
  "CANDLE_CV_CASE16597_DIRECT_GROUPING_OK DEVELOPMENT_NON_RELEASE leaves=1061 function1=1061";;

end;;
