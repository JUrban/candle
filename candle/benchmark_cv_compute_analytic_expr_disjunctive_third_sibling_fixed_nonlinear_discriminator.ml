(* Matched fixed-outer/fixed-nonlinear scan on authentic sibling cells.       *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.                            *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_fixed_nonlinear_discriminator = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Test_cv_compute_analytic_expr_disjunctive_next_sibling_batch_scan;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let candle_cv_fsn_discriminator_jobs_scan_def = define
 `(candle_cv_fsn_discriminator_jobs_scan source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_discriminator_jobs_scan source_program
      (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_variable_raw_jobs_check source_program
         (Cexp_pair job (Cexp_num 0)))
       (candle_cv_fsn_discriminator_jobs_scan source_program jobs))`;;

let candle_cv_fsn_discriminator_jobs_scan_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_discriminator_jobs_scan source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_variable_raw_jobs_check source_program
           (Cexp_pair (Cexp_fst jobs) (Cexp_num 0)))
         (candle_cv_fsn_discriminator_jobs_scan source_program
           (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_discriminator_jobs_scan_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fsn_discriminator_jobs_scan_compute_eqs =
  union candle_cv_fixed_nonlinear_compute_eqs
    [SPEC_ALL candle_cv_fsn_discriminator_jobs_scan_compute];;

let candle_disjunctive_fsn_discriminator_jobs =
  candle_disjunctive_float_point_take 128
    candle_disjunctive_float_point_sample1;;

let candle_disjunctive_fsn_discriminator_bounds =
  map
    (fun (_,_,_,domain) ->
      candle_disjunctive_fixed_outer_domain_bounds domain)
    candle_disjunctive_fsn_discriminator_jobs;;

let candle_disjunctive_fsn_discriminator_centers =
  map
    (fun (lower,upper) ->
      candle_q_dim_taylor_model_point_plan_intervals_six
        candle_disjunctive_next_batch_point_plan1 lower upper)
    candle_disjunctive_fsn_discriminator_bounds;;

let candle_disjunctive_fsn_discriminator_cells =
  map2
    (fun (lower,upper) center ->
      {variable_batch_box_intervals =
         map (candle_disjunctive_fixed_outer_widen 5 4) center;
       variable_batch_stable_cell =
         {stable_batch_center_intervals = center;
          stable_batch_lower = lower;
          stable_batch_upper = upper}})
    candle_disjunctive_fsn_discriminator_bounds
    candle_disjunctive_fsn_discriminator_centers;;

let candle_disjunctive_fsn_discriminator_encoded_jobs =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
    candle_disjunctive_fsn_discriminator_cells;;

let candle_disjunctive_fsn_discriminator_program =
  candle_disjunctive_next_batch_prepared1.program_representation_term;;

let candle_disjunctive_fsn_discriminator_outer_call =
  list_mk_comb
    (`candle_cv_fso_variable_jobs_scan`,
     [candle_disjunctive_fsn_discriminator_program;
      candle_disjunctive_fsn_discriminator_encoded_jobs]);;

let candle_disjunctive_fsn_discriminator_fixed_call =
  list_mk_comb
    (`candle_cv_fsn_discriminator_jobs_scan`,
     [candle_disjunctive_fsn_discriminator_program;
      candle_disjunctive_fsn_discriminator_encoded_jobs]);;

let candle_disjunctive_fsn_discriminator_axioms_before = axioms ();;

print_endline
  "CANDLE_CV_FSN_DISCRIMINATOR_OUTER_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_fsn_discriminator_outer_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_variable_jobs_scan_compute_eqs
    candle_disjunctive_fsn_discriminator_outer_call;;
print_endline
  "CANDLE_CV_FSN_DISCRIMINATOR_OUTER_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_fsn_discriminator_outer_count,
    candle_disjunctive_fsn_discriminator_outer_failures =
  candle_cv_fso_variable_jobs_scan_decode "fixed outer discriminator"
    (rand (concl candle_disjunctive_fsn_discriminator_outer_theorem));;

print_endline
  "CANDLE_CV_FSN_DISCRIMINATOR_FIXED_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_fsn_discriminator_fixed_theorem =
  candle_q_dim_analytic_jet_compute
    candle_cv_fsn_discriminator_jobs_scan_compute_eqs
    candle_disjunctive_fsn_discriminator_fixed_call;;
print_endline
  "CANDLE_CV_FSN_DISCRIMINATOR_FIXED_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_fsn_discriminator_fixed_count,
    candle_disjunctive_fsn_discriminator_fixed_failures =
  candle_cv_fso_variable_jobs_scan_decode "fixed nonlinear discriminator"
    (rand (concl candle_disjunctive_fsn_discriminator_fixed_theorem));;

let candle_disjunctive_fsn_discriminator_axioms_after = axioms ();;

let candle_disjunctive_fsn_discriminator_failure_difference =
  List.filter
    (fun index ->
      List.mem index candle_disjunctive_fsn_discriminator_outer_failures <>
      List.mem index candle_disjunctive_fsn_discriminator_fixed_failures)
    (0--127);;

let candle_disjunctive_fsn_discriminator_prefix count items =
  let rec take remaining = function
    | _ when remaining = 0 -> []
    | [] -> []
    | head::tail -> head::take (remaining - 1) tail in
  take count items;;

if length candle_disjunctive_fsn_discriminator_jobs <> 128 ||
   candle_disjunctive_fsn_discriminator_outer_count <> 128 ||
   candle_disjunctive_fsn_discriminator_fixed_count <> 128 ||
   hyp candle_disjunctive_fsn_discriminator_outer_theorem <> [] ||
   hyp candle_disjunctive_fsn_discriminator_fixed_theorem <> [] ||
   not
     (aconv
       (lhand (concl candle_disjunctive_fsn_discriminator_outer_theorem))
       candle_disjunctive_fsn_discriminator_outer_call) ||
   not
     (aconv
       (lhand (concl candle_disjunctive_fsn_discriminator_fixed_theorem))
       candle_disjunctive_fsn_discriminator_fixed_call) ||
   length candle_disjunctive_fsn_discriminator_axioms_after <>
     length candle_disjunctive_fsn_discriminator_axioms_before ||
   not
     (List.for_all
       (fun axiom ->
         List.mem axiom candle_disjunctive_fsn_discriminator_axioms_before)
       candle_disjunctive_fsn_discriminator_axioms_after) then
  failwith "fixed nonlinear discriminator: validation failed";;

print_endline
  ("CANDLE_CV_FSN_DISCRIMINATOR_OK DEVELOPMENT_NON_RELEASE" ^
   " jobs=128" ^
   " outer_accepted=" ^
   string_of_int
     (128 - length candle_disjunctive_fsn_discriminator_outer_failures) ^
   " outer_rejected=" ^
   string_of_int
     (length candle_disjunctive_fsn_discriminator_outer_failures) ^
   " fixed_accepted=" ^
   string_of_int
     (128 - length candle_disjunctive_fsn_discriminator_fixed_failures) ^
   " fixed_rejected=" ^
   string_of_int
     (length candle_disjunctive_fsn_discriminator_fixed_failures) ^
   " differing_verdicts=" ^
   string_of_int
     (length candle_disjunctive_fsn_discriminator_failure_difference) ^
   " first_differing_indices=" ^
   candle_cv_fso_variable_jobs_scan_indices_string
     (candle_disjunctive_fsn_discriminator_prefix 16
       candle_disjunctive_fsn_discriminator_failure_difference) ^
   " assumptions=0 axiom_growth=0");;

end;;
