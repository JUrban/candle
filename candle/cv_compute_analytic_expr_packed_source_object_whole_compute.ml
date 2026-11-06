(* ========================================================================== *)
(* Whole-call executable boundary for explicit-radius packed object jobs.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the missing executable composition    *)
(* point between the exact-object per-cell entry and the already proved       *)
(* compact topology runner.                                                   *)
(*                                                                            *)
(* The source descriptor is                                                   *)
(*                                                                            *)
(*   (plan codes,(source instructions,packed cells)),                         *)
(*                                                                            *)
(* where each packed cell is (radii,certificates).  The packed-cell stream    *)
(* and job stream are consumed in lockstep and must end together.             *)
(*                                                                            *)
(* Every encoded job is                                                       *)
(*                                                                            *)
(*   (outer boxes,(center boxes,source boxes)).                                *)
(*                                                                            *)
(* This is exactly the existing variable-job representation.  In particular, *)
(* [SND (SND job)] is the source box consumed by the compact topology runner. *)
(* Keeping that representation unchanged lets its existing decoder and        *)
(* soundness theorem remain applicable.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_entry.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Candle_cv_analytic_expr_packed_source_object_whole_compute = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;

let candle_cv_q_packed_object_whole_job_check_def = new_definition
 `candle_cv_q_packed_object_whole_job_check
      plan_codes source_instructions packed_cell job =
    let outer_boxes = Cexp_fst job in
    let center_boxes = Cexp_fst (Cexp_snd job) in
    let radii = Cexp_fst packed_cell in
    let certificates = Cexp_snd packed_cell in
    candle_cv_q_packed_object_dispatch_entry
      center_boxes outer_boxes radii plan_codes source_instructions
      certificates`;;

(* Numeric zero is the sole canonical terminator for both lists.  Pair/number *)
(* shape disagreement, a nonzero terminator, or a failed entry rejects.       *)
let candle_cv_q_packed_object_whole_jobs_check_def = define
 `(candle_cv_q_packed_object_whole_jobs_check
      plan_codes source_instructions (Cexp_num packed_end)
      (Cexp_num jobs_end) =
    candle_cv_bool_and
      (Cexp_eq (Cexp_num packed_end) (Cexp_num 0))
      (Cexp_eq (Cexp_num jobs_end) (Cexp_num 0))) /\
  (candle_cv_q_packed_object_whole_jobs_check
      plan_codes source_instructions (Cexp_num packed_end)
      (Cexp_pair job jobs) = Cexp_num 0) /\
  (candle_cv_q_packed_object_whole_jobs_check
      plan_codes source_instructions (Cexp_pair packed_cell packed_cells)
      (Cexp_num jobs_end) = Cexp_num 0) /\
  (candle_cv_q_packed_object_whole_jobs_check
      plan_codes source_instructions (Cexp_pair packed_cell packed_cells)
      (Cexp_pair job jobs) =
    candle_cv_bool_and
      (Cexp_eq
        (candle_cv_q_packed_object_whole_job_check
          plan_codes source_instructions packed_cell job)
        (Cexp_num 1))
      (candle_cv_q_packed_object_whole_jobs_check
        plan_codes source_instructions packed_cells jobs))`;;

(* Return both verdicts, rather than collapsing them prematurely.  The       *)
(* soundness layer can then expose the exact numerical and topology premises *)
(* and the final handoff can additionally require an empty job remainder and *)
(* singleton root stack.                                                      *)
let candle_cv_q_packed_object_whole_check_def = new_definition
 `candle_cv_q_packed_object_whole_check
      source_descriptor tree_dim tokens encoded_jobs =
    let plan_codes = Cexp_fst source_descriptor in
    let source_and_cells = Cexp_snd source_descriptor in
    let source_instructions = Cexp_fst source_and_cells in
    let packed_cells = Cexp_snd source_and_cells in
    Cexp_pair
      (candle_cv_q_packed_object_whole_jobs_check
        plan_codes source_instructions packed_cells encoded_jobs)
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
        tree_dim tokens encoded_jobs (Cexp_num 0))`;;

let candle_cv_q_packed_object_whole_compute_eqs () =
  union
    ([SPEC_ALL candle_cv_q_packed_object_whole_job_check_def;
      SPEC_ALL candle_cv_q_packed_object_whole_check_def] @
     CONJUNCTS candle_cv_q_packed_object_whole_jobs_check_def)
    candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_compute_eqs;;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_COMPUTE_OK DEVELOPMENT_NON_RELEASE";;

end;;
