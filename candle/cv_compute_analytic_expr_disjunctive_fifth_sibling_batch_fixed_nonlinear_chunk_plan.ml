(* Whole-component bounded batches for the fifth authentic sibling forest.   *)

needs "candle/cv_compute_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan.ml";;

module Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_fixed_nonlinear_chunk_plan = struct

open Candle_cv_analytic_expr_disjunctive_next_sibling_batch_forest_plan;;
open Candle_cv_analytic_expr_disjunctive_fifth_sibling_batch_forest_plan;;

let candle_disjunctive_fifth_chunk_cell_limit = 128;;

(* Function 0 of the fourth batch established this ceiling with the same
   checker equations.  A larger indivisible component must fail here rather
   than silently reintroduce the exhausted monolithic computation. *)
let candle_disjunctive_fifth_chunk_validated_cell_ceiling = 2170;;

let rec candle_disjunctive_fifth_chunk_shape_cells = function
  | Candle_disjunctive_next_batch_leaf _ -> 1
  | Candle_disjunctive_next_batch_node (_,_,left,right) ->
      candle_disjunctive_fifth_chunk_shape_cells left +
      candle_disjunctive_fifth_chunk_shape_cells right;;

let candle_disjunctive_fifth_chunk_component_cells component =
  candle_disjunctive_fifth_chunk_shape_cells
    component.next_batch_component_shape;;

let candle_disjunctive_fifth_chunk_components components =
  let rec build current current_cells completed remaining =
    match remaining with
    | [] ->
        rev
          (match current with
           | [] -> completed
           | _ -> (rev current)::completed)
    | component::tail ->
        let component_cells =
          candle_disjunctive_fifth_chunk_component_cells component in
        (match current with
         | _::_ when
             current_cells + component_cells >
               candle_disjunctive_fifth_chunk_cell_limit ->
             build [component] component_cells
               ((rev current)::completed) tail
         | _ ->
             build (component::current) (current_cells + component_cells)
               completed tail) in
  build [] 0 [] components;;

let candle_disjunctive_fifth_chunk_max_cells groups =
  List.fold_left
    (fun maximum components ->
      let cells =
        List.fold_left
          (fun total component ->
            total + candle_disjunctive_fifth_chunk_component_cells component)
          0 components in
      max maximum cells)
    0 groups;;

let candle_disjunctive_fifth_chunk_total_cells groups =
  List.fold_left
    (fun total components ->
      List.fold_left
        (fun subtotal component ->
          subtotal + candle_disjunctive_fifth_chunk_component_cells component)
        total components)
    0 groups;;

let candle_disjunctive_fifth_chunk_total_components groups =
  List.fold_left
    (fun total components -> total + length components)
    0 groups;;

let candle_disjunctive_fifth_chunk_oversized_singletons groups =
  List.fold_left
    (fun count components ->
      let cells =
        List.fold_left
          (fun total component ->
            total + candle_disjunctive_fifth_chunk_component_cells component)
          0 components in
      if cells <= candle_disjunctive_fifth_chunk_cell_limit then count
      else if length components = 1 then count + 1
      else failwith
        "fifth fixed-nonlinear chunk plan: oversized multi-component group")
    0 groups;;

let candle_disjunctive_fifth_chunk_function0_groups_get =
  let groups =
    candle_disjunctive_fifth_chunk_components
      candle_disjunctive_fifth_batch_components0 in
  fun () -> groups;;
let candle_disjunctive_fifth_chunk_function1_groups_get =
  let groups =
    candle_disjunctive_fifth_chunk_components
      candle_disjunctive_fifth_batch_components1 in
  fun () -> groups;;

let candle_disjunctive_fifth_chunk_function0_max_cells =
  candle_disjunctive_fifth_chunk_max_cells
    (candle_disjunctive_fifth_chunk_function0_groups_get ());;
let candle_disjunctive_fifth_chunk_function1_max_cells =
  candle_disjunctive_fifth_chunk_max_cells
    (candle_disjunctive_fifth_chunk_function1_groups_get ());;

if candle_disjunctive_fifth_chunk_function0_max_cells >
     candle_disjunctive_fifth_chunk_validated_cell_ceiling ||
   candle_disjunctive_fifth_chunk_function1_max_cells >
     candle_disjunctive_fifth_chunk_validated_cell_ceiling ||
   candle_disjunctive_fifth_chunk_total_cells
     (candle_disjunctive_fifth_chunk_function0_groups_get ()) <>
     length candle_disjunctive_fifth_batch_cells0 ||
   candle_disjunctive_fifth_chunk_total_cells
     (candle_disjunctive_fifth_chunk_function1_groups_get ()) <>
     length candle_disjunctive_fifth_batch_cells1 ||
   candle_disjunctive_fifth_chunk_total_components
     (candle_disjunctive_fifth_chunk_function0_groups_get ()) <>
     length candle_disjunctive_fifth_batch_components0 ||
   candle_disjunctive_fifth_chunk_total_components
     (candle_disjunctive_fifth_chunk_function1_groups_get ()) <>
     length candle_disjunctive_fifth_batch_components1 then
  failwith
    ("fifth fixed-nonlinear chunk plan: accounting drift" ^
     " function0_max_cells=" ^
     string_of_int candle_disjunctive_fifth_chunk_function0_max_cells ^
     " function1_max_cells=" ^
     string_of_int candle_disjunctive_fifth_chunk_function1_max_cells ^
     " function0_group_cells=" ^
     string_of_int
       (candle_disjunctive_fifth_chunk_total_cells
         (candle_disjunctive_fifth_chunk_function0_groups_get ())) ^
     " function1_group_cells=" ^
     string_of_int
       (candle_disjunctive_fifth_chunk_total_cells
         (candle_disjunctive_fifth_chunk_function1_groups_get ())) ^
     " function0_group_components=" ^
     string_of_int
       (candle_disjunctive_fifth_chunk_total_components
         (candle_disjunctive_fifth_chunk_function0_groups_get ())) ^
     " function1_group_components=" ^
     string_of_int
       (candle_disjunctive_fifth_chunk_total_components
         (candle_disjunctive_fifth_chunk_function1_groups_get ())));;

print_endline
  ("CANDLE_CV_FIFTH_SIBLING_BATCH_FIXED_NONLINEAR_CHUNK_PLAN_OK" ^
   " DEVELOPMENT_NON_RELEASE cell_limit=" ^
   string_of_int candle_disjunctive_fifth_chunk_cell_limit ^
   " validated_cell_ceiling=" ^
   string_of_int candle_disjunctive_fifth_chunk_validated_cell_ceiling ^
   " function0_groups=" ^
   string_of_int
     (length (candle_disjunctive_fifth_chunk_function0_groups_get ())) ^
   " function0_max_cells=" ^
   string_of_int candle_disjunctive_fifth_chunk_function0_max_cells ^
   " function0_oversized_singletons=" ^
   string_of_int
     (candle_disjunctive_fifth_chunk_oversized_singletons
       (candle_disjunctive_fifth_chunk_function0_groups_get ())) ^
   " function1_groups=" ^
   string_of_int
     (length (candle_disjunctive_fifth_chunk_function1_groups_get ())) ^
   " function1_max_cells=" ^
   string_of_int candle_disjunctive_fifth_chunk_function1_max_cells ^
   " function1_oversized_singletons=" ^
   string_of_int
     (candle_disjunctive_fifth_chunk_oversized_singletons
       (candle_disjunctive_fifth_chunk_function1_groups_get ())));;

end;;
