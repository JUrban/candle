(* Focused first-group test for the checkpointable fourth function-0 lane. *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state.ml";;

module Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_first_group = struct

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state;;

let candle_disjunctive_fourth_bounded_f0_axioms_before = axioms ();;

let _ = candle_disjunctive_fourth_bounded_f0_advance 1;;

let candle_disjunctive_fourth_bounded_f0_first_progress =
  candle_disjunctive_fourth_bounded_f0_progress_get ();;

let candle_disjunctive_fourth_bounded_f0_first_sources =
  candle_disjunctive_fourth_bounded_f0_completed_sources ();;

let candle_disjunctive_fourth_bounded_f0_axioms_after = axioms ();;

if candle_disjunctive_fourth_bounded_f0_first_progress.
     fourth_bounded_f0_completed_groups <> 1 ||
   candle_disjunctive_fourth_bounded_f0_first_progress.
     fourth_bounded_f0_remaining_groups <>
     length (candle_disjunctive_fourth_chunk_function0_groups_get ()) - 1 ||
   candle_disjunctive_fourth_bounded_f0_first_progress.
     fourth_bounded_f0_completed_cells <= 0 ||
   candle_disjunctive_fourth_bounded_f0_first_progress.
     fourth_bounded_f0_completed_cells >
     candle_disjunctive_fourth_chunk_cell_limit ||
   candle_disjunctive_fourth_bounded_f0_first_progress.
     fourth_bounded_f0_completed_roots <>
     length candle_disjunctive_fourth_bounded_f0_first_sources ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       candle_disjunctive_fourth_bounded_f0_first_sources) ||
   length candle_disjunctive_fourth_bounded_f0_axioms_after <>
     length candle_disjunctive_fourth_bounded_f0_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fourth_bounded_f0_axioms_before)
       candle_disjunctive_fourth_bounded_f0_axioms_after) then
  failwith "fourth bounded function0 first group: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FUNCTION0_FIRST_GROUP_OK" ^
   " DEVELOPMENT_NON_RELEASE cells=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_first_progress.
       fourth_bounded_f0_completed_cells ^
   " roots=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_first_progress.
       fourth_bounded_f0_completed_roots ^
   " assumptions=0 frees=0 axiom_growth=0");;

end;;
