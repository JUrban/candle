(* Advance four independently sealed function-0 groups from a fresh          *)
(* checkpoint.  Seventeen total groups means the first-group probe followed  *)
(* by four applications of this fragment closes the entire function.         *)

needs "candle/cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state.ml";;

module Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_advance4 = struct

open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_chunk_plan;;
open Candle_cv_analytic_expr_disjunctive_fourth_sibling_batch_fixed_nonlinear_bounded_function0_state;;

let candle_disjunctive_fourth_bounded_f0_advance4_axioms_before = axioms ();;

let _ = candle_disjunctive_fourth_bounded_f0_advance 4;;

let candle_disjunctive_fourth_bounded_f0_advance4_progress =
  candle_disjunctive_fourth_bounded_f0_progress_get ();;

let candle_disjunctive_fourth_bounded_f0_advance4_sources =
  candle_disjunctive_fourth_bounded_f0_completed_sources ();;

let candle_disjunctive_fourth_bounded_f0_advance4_axioms_after = axioms ();;

if candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_completed_groups <= 1 ||
   candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_completed_groups >
     length (candle_disjunctive_fourth_chunk_function0_groups_get ()) ||
   candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_remaining_groups < 0 ||
   candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_completed_groups +
     candle_disjunctive_fourth_bounded_f0_advance4_progress.
       fourth_bounded_f0_remaining_groups <>
     length (candle_disjunctive_fourth_chunk_function0_groups_get ()) ||
   candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_completed_roots <>
     length candle_disjunctive_fourth_bounded_f0_advance4_sources ||
   candle_disjunctive_fourth_bounded_f0_advance4_progress.
     fourth_bounded_f0_max_group_cells >
     candle_disjunctive_fourth_chunk_cell_limit ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [] && frees (concl theorem) = [])
       candle_disjunctive_fourth_bounded_f0_advance4_sources) ||
   length candle_disjunctive_fourth_bounded_f0_advance4_axioms_after <>
     length candle_disjunctive_fourth_bounded_f0_advance4_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom
           candle_disjunctive_fourth_bounded_f0_advance4_axioms_before)
       candle_disjunctive_fourth_bounded_f0_advance4_axioms_after) then
  failwith "fourth bounded function0 advance4: validation failed";;

print_endline
  ("CANDLE_CV_FOURTH_SIBLING_BATCH_FIXED_NONLINEAR_BOUNDED_FUNCTION0_ADVANCE4_OK" ^
   " DEVELOPMENT_NON_RELEASE completed_groups=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_advance4_progress.
       fourth_bounded_f0_completed_groups ^
   " remaining_groups=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_advance4_progress.
       fourth_bounded_f0_remaining_groups ^
   " completed_cells=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_advance4_progress.
       fourth_bounded_f0_completed_cells ^
   " completed_roots=" ^
   string_of_int
     candle_disjunctive_fourth_bounded_f0_advance4_progress.
       fourth_bounded_f0_completed_roots ^
   " assumptions=0 frees=0 axiom_growth=0");;

end;;
