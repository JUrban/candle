(* ========================================================================== *)
(* Pure plan data and domain expansion for action-296-style leaf forests.    *)
(*                                                                            *)
(* A plan is untrusted ordinary data.  Expanding it constructs only the      *)
(* corresponding exact domain theorems; numerical acceptance and source      *)
(* soundness remain responsibilities of the proof/checker adapters.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_leaf_grouping_fixture.ml";;

module Candle_cv_action296_forest_plan = struct

open Candle_cv_analytic_expr_action296_plan;;

type candle_action296_forest_plan =
  | Candle_action296_forest_leaf
  | Candle_action296_forest_split of
      int * candle_action296_forest_plan * candle_action296_forest_plan;;

type candle_action296_forest_tree =
  | Candle_action296_forest_tree_leaf of thm
  | Candle_action296_forest_tree_split of
      int * candle_action296_forest_tree * candle_action296_forest_tree;;

let rec candle_action296_forest_build_tree domain = function
  | Candle_action296_forest_leaf ->
      Candle_action296_forest_tree_leaf domain
  | Candle_action296_forest_split (axis,left_plan,right_plan) ->
      if axis < 1 || axis > 6 then
        failwith "action296 forest plan: split axis out of range";
      let left,right =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain in
      Candle_action296_forest_tree_split
        (axis,
         candle_action296_forest_build_tree left left_plan,
         candle_action296_forest_build_tree right right_plan);;

let rec candle_action296_forest_tree_domains = function
  | Candle_action296_forest_tree_leaf domain -> [domain]
  | Candle_action296_forest_tree_split (_,left,right) ->
      candle_action296_forest_tree_domains left @
      candle_action296_forest_tree_domains right;;

end;;
