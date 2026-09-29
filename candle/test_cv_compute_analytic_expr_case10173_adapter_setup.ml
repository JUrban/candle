(* Fail-closed setup checks for the shared-expression sibling forest. *)

open Candle_cv_analytic_expr_action296_fixture;;
open Candle_cv_analytic_expr_case10173_fixture;;
open Candle_cv_action296_adaptive_forest_prove;;

if not
     (aconv candle_case10173_analytic_function
        candle_action296_analytic_function) ||
   length !candle_action296_leaf_grouping_leaves <> 3305 ||
   not
     (candle_action296_forest_strict_roots (-1)
       [(3304,Candle_action296_forest_leaf)]) ||
   candle_action296_forest_strict_roots (-1)
     [(3305,Candle_action296_forest_leaf)] ||
   candle_action296_forest_strict_roots (-1)
     [(0,Candle_action296_forest_leaf);
      (0,Candle_action296_forest_leaf)] then
  failwith "case10173 forest adapter: setup contract failed";;

print_endline
  "CANDLE_CV_CASE10173_ADAPTER_SETUP_OK DEVELOPMENT_NON_RELEASE";;
