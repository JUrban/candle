(* Authentic 635-cell group-83 proof with both numerical and topology size    *)
(* bounded at 128 cells, followed by kernel-checked split reconstruction.     *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunked_function1_state.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_component_bounded_prove.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_group83_bounded_component = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Candle_cv_analytic_expr_disjunctive_component_bounded_prove;;

let rec candle_disjunctive_fourth_group83_bounded_nth index = function
  | [] -> failwith "fourth group83 bounded component: group underflow"
  | head::tail ->
      if index = 0 then head
      else candle_disjunctive_fourth_group83_bounded_nth (index - 1) tail;;

let candle_disjunctive_fourth_group83_bounded_components =
  candle_disjunctive_fourth_group83_bounded_nth 83
    (candle_disjunctive_fourth_chunk_function1_groups_get ());;

let candle_disjunctive_fourth_group83_bounded_component =
  match candle_disjunctive_fourth_group83_bounded_components with
  | [component] -> component
  | _ -> failwith "fourth group83 bounded component: non-singleton group";;

let candle_disjunctive_fourth_group83_bounded_cells =
  candle_disjunctive_component_bounded_shape_cells
    candle_disjunctive_fourth_group83_bounded_component.
      next_batch_component_shape;;

let candle_disjunctive_fourth_group83_bounded_axioms_before = axioms ();;

let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-function1-group83-bounded-component-begin";;
let candle_disjunctive_fourth_group83_bounded_result =
  candle_disjunctive_component_bounded_prove
    candle_disjunctive_next_batch_prepared1 128
    candle_disjunctive_fourth_group83_bounded_component;;
let _ =
  candle_q_dim_analytic_jet_profile_event
    "fourth-sibling-function1-group83-bounded-component-end";;

let candle_disjunctive_fourth_group83_bounded_axioms_after = axioms ();;

if length candle_disjunctive_fourth_group83_bounded_cells <> 635 ||
   candle_disjunctive_fourth_group83_bounded_result.
     component_bounded_numerical_batches <= 1 ||
   candle_disjunctive_fourth_group83_bounded_result.
     component_bounded_reflected_subtrees <= 1 ||
   candle_disjunctive_fourth_group83_bounded_result.
     component_bounded_max_subtree_cells > 128 ||
   hyp
     candle_disjunctive_fourth_group83_bounded_result.
       component_bounded_list_theorem <> [] ||
   frees
     (concl
       candle_disjunctive_fourth_group83_bounded_result.
         component_bounded_list_theorem) <> [] ||
   length candle_disjunctive_fourth_group83_bounded_axioms_after <>
     length candle_disjunctive_fourth_group83_bounded_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_group83_bounded_axioms_before)
       candle_disjunctive_fourth_group83_bounded_axioms_after) then
  failwith "fourth group83 bounded component: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_GROUP83_BOUNDED_COMPONENT_OK" ^
   " DEVELOPMENT_NON_RELEASE cells=635 raw_batches=" ^
   string_of_int
     candle_disjunctive_fourth_group83_bounded_result.
       component_bounded_numerical_batches ^
   " reflected_subtrees=" ^
   string_of_int
     candle_disjunctive_fourth_group83_bounded_result.
       component_bounded_reflected_subtrees ^
   " max_subtree_cells=" ^
   string_of_int
     candle_disjunctive_fourth_group83_bounded_result.
       component_bounded_max_subtree_cells ^
   " roots=1 assumptions=0 frees=0 axiom_growth=0");;

end;;
