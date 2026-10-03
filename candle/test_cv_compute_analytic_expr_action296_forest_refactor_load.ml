(* Focused load/type regression for the shared pure adaptive-forest plan. *)

needs "candle/cv_compute_analytic_expr_action296_adaptive_forest_prove.ml";;
needs "candle/cv_compute_analytic_expr_case10173_fixed_outer_generated_plan.ml";;

module Test_cv_compute_analytic_expr_action296_forest_refactor_load = struct

open Candle_cv_action296_forest_plan;;
open Candle_cv_action296_adaptive_forest_prove;;

let _ =
  let axioms_before = axioms () in
  if length candle_action296_generated_roots <> 3305 ||
     candle_action296_generated_final_cells <> 4173 ||
     not
       (candle_action296_forest_strict_roots
         (-1) candle_action296_generated_roots) then
    failwith "action296 forest refactor load: generated plan drift";
  let _,first_plan = hd candle_action296_generated_roots in
  let first_parent = hd !candle_action296_leaf_grouping_leaves in
  let first_tree =
    candle_action296_forest_build_tree first_parent first_plan in
  let first_domains = candle_action296_forest_tree_domains first_tree in
  let axioms_after = axioms () in
  if first_domains = [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "action296 forest refactor load: validation failed";
  print_endline
    "CANDLE_CV_ACTION296_FOREST_REFACTOR_LOAD_OK DEVELOPMENT_NON_RELEASE roots=3305 cells=4173 axiom_growth=0";;

end;;
