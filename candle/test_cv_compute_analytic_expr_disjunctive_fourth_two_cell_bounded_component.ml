(* Cheap authentic split/reconstruction test for the bounded component path. *)

needs "candle/cv_compute_analytic_expr_disjunctive_component_bounded_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_two_cell_bounded_component = struct

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_component_bounded_prove;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;

let rec candle_disjunctive_fourth_two_cell_component = function
  | [] -> failwith "fourth two-cell bounded component: no fixture"
  | component::remaining ->
      if length
           (candle_disjunctive_component_bounded_shape_cells
             component.next_batch_component_shape) = 2 then
        component
      else
        candle_disjunctive_fourth_two_cell_component remaining;;

let candle_disjunctive_fourth_two_cell_fixture =
  candle_disjunctive_fourth_two_cell_component
    candle_disjunctive_fourth_batch_components1;;

let candle_disjunctive_fourth_two_cell_axioms_before = axioms ();;
let candle_disjunctive_fourth_two_cell_result =
  candle_disjunctive_component_bounded_prove
    candle_disjunctive_next_batch_prepared1 1
    candle_disjunctive_fourth_two_cell_fixture;;
let candle_disjunctive_fourth_two_cell_axioms_after = axioms ();;

if candle_disjunctive_fourth_two_cell_result.
     component_bounded_numerical_batches <> 2 ||
   candle_disjunctive_fourth_two_cell_result.
     component_bounded_reflected_subtrees <> 2 ||
   candle_disjunctive_fourth_two_cell_result.
     component_bounded_max_subtree_cells <> 1 ||
   hyp candle_disjunctive_fourth_two_cell_result.
     component_bounded_list_theorem <> [] ||
   frees
     (concl candle_disjunctive_fourth_two_cell_result.
       component_bounded_list_theorem) <> [] ||
   length candle_disjunctive_fourth_two_cell_axioms_after <>
     length candle_disjunctive_fourth_two_cell_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_two_cell_axioms_before)
       candle_disjunctive_fourth_two_cell_axioms_after) then
  failwith "fourth two-cell bounded component: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_TWO_CELL_BOUNDED_COMPONENT_OK" ^
   " DEVELOPMENT_NON_RELEASE cells=2 raw_batches=2" ^
   " reflected_subtrees=2 max_subtree_cells=1" ^
   " roots=1 assumptions=0 frees=0 axiom_growth=0");;

end;;
