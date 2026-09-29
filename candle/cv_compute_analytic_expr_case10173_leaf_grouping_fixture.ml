(* ========================================================================== *)
(* Genuine case-10173 leaves through the shared-expression forest adapter.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The global leaf reference belongs to the      *)
(* isolated restored experiment and is deliberately replaced only after the *)
(* full sibling certificate tree has been authenticated and traversed.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_case10173_reused_plan.ml";;

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_case10173_reused_plan;;

let candle_case10173_leaf_grouping_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_case10173_plan_xx1 candle_case10173_plan_zz1;;

let candle_case10173_leaf_grouping_leaves =
  candle_action296_leaf_grouping_collect
    candle_case10173_leaf_grouping_root_domain
    candle_case10173_plan_precision_tree;;

if length candle_case10173_leaf_grouping_leaves <> 3305 then
  failwith "case10173 leaf grouping: leaf cardinality drift";;

let _ =
  candle_action296_leaf_grouping_leaves :=
    candle_case10173_leaf_grouping_leaves;;

print_endline
  "CANDLE_CV_CASE10173_LEAF_GROUPING_OK leaves=3305 DEVELOPMENT_NON_RELEASE";;
