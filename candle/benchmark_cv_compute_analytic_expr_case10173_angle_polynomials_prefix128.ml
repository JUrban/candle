(* ========================================================================== *)
(* Centered angle-polynomial Kernel.compute discriminator on case 10173.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The temporary dispatch     *)
(* recognizes the genuine 85-instruction polynomial by length only.  This is *)
(* suitable solely for measuring the numerical implementation.  Production   *)
(* use requires exact authenticated compiled-program identity plus the general*)
(* containment theorem.                                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_angle_polynomials_compute.ml";;
needs "candle/benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_angle_polynomials_prefix128 = struct

open Candle_cv_analytic_expr_fixed_scale_angle_polynomials_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_cval_list;;
open Benchmark_cv_compute_analytic_expr_case10173_bound_tightness_prefix128;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

let candle_cv_fsn_angle_program_step_def = new_definition
 `candle_cv_fsn_angle_program_step
      center_boxes boxes radii center_instruction box_instruction stack =
    Cexp_if (Cexp_ispair center_instruction)
      (Cexp_if (Cexp_ispair box_instruction)
        (Cexp_if (Cexp_eq (Cexp_fst center_instruction) (Cexp_num 0))
          (Cexp_if (Cexp_eq (Cexp_fst box_instruction) (Cexp_num 0))
            (Cexp_if
              (Cexp_eq (candle_cv_list_length
                (Cexp_snd center_instruction)) (Cexp_num 85))
              (Cexp_pair
                (candle_cv_fsa_item_fixed
                  (candle_cv_fs_angle_four_x0_delta_q
                    center_boxes boxes radii))
                stack)
              (candle_cv_fso_program_step_fixed_nonlinear
                center_boxes boxes radii center_instruction box_instruction
                stack))
            (candle_cv_fso_program_step_fixed_nonlinear
              center_boxes boxes radii center_instruction box_instruction
              stack))
          (candle_cv_fso_program_step_fixed_nonlinear
            center_boxes boxes radii center_instruction box_instruction
            stack))
        (candle_cv_fso_program_step_fixed_nonlinear
          center_boxes boxes radii center_instruction box_instruction stack))
      (candle_cv_fso_program_step_fixed_nonlinear
        center_boxes boxes radii center_instruction box_instruction stack)`;;

let candle_cv_fsn_angle_program_run_def = define
 `(candle_cv_fsn_angle_program_run
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fsn_angle_program_run
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fsn_angle_program_run
     center_boxes boxes radii
     (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fsn_angle_program_run center_boxes boxes radii ct bt
       (candle_cv_fsn_angle_program_step
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fsn_angle_program_run_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fsn_angle_program_run
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fsn_angle_program_run center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fsn_angle_program_step center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsn_angle_program_run_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fsn_angle_program_def = new_definition
 `candle_cv_fsn_angle_program center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fsn_angle_program_run
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fsn_angle_certified_check_def = new_definition
 `candle_cv_fsn_angle_certified_check center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fsn_angle_program center_program box_program boxes)`;;

let candle_cv_fsn_angle_variable_job_bound_def = new_definition
 `candle_cv_fsn_angle_variable_job_bound source_program job =
    Cexp_if
      (candle_cv_analytic_program_sqrt_data_exact
        (Cexp_fst job) source_program)
      (let box_patched =
         candle_cv_analytic_program_patch_sqrt
           (Cexp_fst job) source_program in
       Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_snd job)) source_program)
         (let center_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_snd job)) source_program in
          candle_cv_fsn_angle_certified_check
            (Cexp_snd center_patched) (Cexp_snd box_patched)
            (Cexp_snd (Cexp_snd job)))
         (Cexp_pair (Cexp_num 0) (Cexp_num 0)))
      (Cexp_pair (Cexp_num 0) (Cexp_num 0))`;;

let candle_cv_fsn_angle_variable_jobs_bounds_def = define
 `(candle_cv_fsn_angle_variable_jobs_bounds source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_angle_variable_jobs_bounds
     source_program (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_angle_variable_job_bound source_program job)
       (candle_cv_fsn_angle_variable_jobs_bounds source_program jobs))`;;

let candle_cv_fsn_angle_variable_jobs_bounds_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_angle_variable_jobs_bounds source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_angle_variable_job_bound
           source_program (Cexp_fst jobs))
         (candle_cv_fsn_angle_variable_jobs_bounds
           source_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fsn_angle_variable_jobs_bounds_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_case10173_angle_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fs_angle_compute_eqs
      (map SPEC_ALL
        [candle_cv_list_length_compute;
         candle_cv_fsn_angle_program_step_def;
         candle_cv_fsn_angle_program_run_compute;
         candle_cv_fsn_angle_program_def;
         candle_cv_fsn_angle_certified_check_def;
         candle_cv_fsn_angle_variable_job_bound_def;
         candle_cv_fsn_angle_variable_jobs_bounds_compute]));;

let _ =
  let axioms_before = axioms () in
  let baseline =
    match !candle_case10173_bound_prefix128_theorem with
    | Some theorem -> theorem
    | None -> failwith "case10173 angle polynomial: baseline unavailable" in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-angle-polynomials-prefix128" ^
         " phase=" ^ event));
  candle_q_dim_analytic_jet_profile_event "encoding-begin";
  let plan = candle_case10173_variable_raw_plan () in
  let cells =
    candle_case10173_bound_prefix_take 128
      plan.case10173_variable_raw_plan_cells in
  let encoded_jobs =
    candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
      cells in
  candle_q_dim_analytic_jet_profile_event "encoding-end";
  let call =
    list_mk_comb
      (`candle_cv_fsn_angle_variable_jobs_bounds`,
       [plan.case10173_variable_raw_plan_prepared.program_representation_term;
        encoded_jobs]) in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-begin";
  let candidate =
    candle_q_dim_analytic_jet_compute
      candle_case10173_angle_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-end";
  if hyp candidate <> [] ||
     not (aconv (rand (concl baseline)) (rand (concl candidate))) then
    failwith "case10173 angle polynomial: exact result mismatch";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 angle polynomial: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_ANGLE_POLYNOMIALS_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 temporary_length_dispatch=1 exact_match=1 assumptions=0 axiom_growth=0";;

end;;
