(* ========================================================================== *)
(* Shared-nonlinear-subexpression timing on 128 genuine case-10173 cells.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The candidate step is proved exactly equal to *)
(* the established step.  This matched run measures only whether retaining   *)
(* the repeated rational derivative intervals helps Kernel.compute.           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_nonlinear_shared.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_nonlinear_shared_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_shared;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fso_program_step_nonlinear_select_def = new_definition
 `candle_cv_fso_program_step_nonlinear_select
      use_shared center_boxes boxes radii
      center_instruction box_instruction stack =
    Cexp_if use_shared
      (candle_cv_fso_program_step_nonlinear_shared
        center_boxes boxes radii center_instruction box_instruction stack)
      (candle_cv_fso_program_step
        center_boxes boxes radii center_instruction box_instruction stack)`;;

let candle_cv_fso_program_run_nonlinear_select_def = define
 `(candle_cv_fso_program_run_nonlinear_select
     use_shared center_boxes boxes radii
     (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fso_program_run_nonlinear_select
     use_shared center_boxes boxes radii
     (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fso_program_run_nonlinear_select
     use_shared center_boxes boxes radii
     (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fso_program_run_nonlinear_select
       use_shared center_boxes boxes radii ct bt
       (candle_cv_fso_program_step_nonlinear_select use_shared
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fso_program_run_nonlinear_select_compute = prove
 (`!use_shared center_boxes boxes radii center_program box_program stack.
     candle_cv_fso_program_run_nonlinear_select
       use_shared center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fso_program_run_nonlinear_select
           use_shared center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fso_program_step_nonlinear_select use_shared
             center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_program_run_nonlinear_select_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_program_nonlinear_select_def = new_definition
 `candle_cv_fso_program_nonlinear_select
      use_shared center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fso_program_run_nonlinear_select use_shared
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fso_certified_check_nonlinear_select_def = new_definition
 `candle_cv_fso_certified_check_nonlinear_select
      use_shared center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fso_program_nonlinear_select
        use_shared center_program box_program boxes)`;;

let candle_cv_fso_variable_jobs_check_nonlinear_select_def = define
 `(candle_cv_fso_variable_jobs_check_nonlinear_select
      use_shared source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_variable_jobs_check_nonlinear_select
      use_shared source_program (Cexp_pair job jobs) =
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
           Cexp_if
             (Cexp_fst
               (candle_cv_fso_certified_check_nonlinear_select use_shared
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fso_variable_jobs_check_nonlinear_select
               use_shared source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_variable_jobs_check_nonlinear_select_compute = prove
 (`!use_shared source_program jobs.
     candle_cv_fso_variable_jobs_check_nonlinear_select
       use_shared source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (candle_cv_analytic_program_sqrt_data_exact
           (Cexp_fst (Cexp_fst jobs)) source_program)
         (let box_patched =
            candle_cv_analytic_program_patch_sqrt
              (Cexp_fst (Cexp_fst jobs)) source_program in
          Cexp_if
            (candle_cv_analytic_program_sqrt_data_exact
              (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program)
            (let center_patched =
               candle_cv_analytic_program_patch_sqrt
                 (Cexp_fst (Cexp_snd (Cexp_fst jobs))) source_program in
             Cexp_if
               (Cexp_fst
                 (candle_cv_fso_certified_check_nonlinear_select use_shared
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fso_variable_jobs_check_nonlinear_select
                 use_shared source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_check_nonlinear_select_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_fso_variable_raw_jobs_check_nonlinear_select_def =
  new_definition
   `candle_cv_fso_variable_raw_jobs_check_nonlinear_select
        use_shared source_program encoded_jobs =
      candle_cv_bool_and
        (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
          encoded_jobs)
        (candle_cv_fso_variable_jobs_check_nonlinear_select
          use_shared source_program encoded_jobs)`;;

let candle_case10173_nonlinear_shared_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_nonlinear_shared_compute_eqs
        (map SPEC_ALL
          [candle_cv_fso_program_step_nonlinear_select_def;
           candle_cv_fso_program_run_nonlinear_select_compute;
           candle_cv_fso_program_nonlinear_select_def;
           candle_cv_fso_certified_check_nonlinear_select_def;
           candle_cv_fso_variable_jobs_check_nonlinear_select_compute;
           candle_cv_fso_variable_raw_jobs_check_nonlinear_select_def])));;

let rec candle_case10173_nonlinear_shared_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 nonlinear-shared prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_nonlinear_shared_cval_take (count - 1) tail);;

let candle_case10173_nonlinear_shared_validate call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv (rand (concl theorem)) `Cexp_num 1`;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-nonlinear-shared-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let encoded_jobs =
    candle_case10173_nonlinear_shared_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let call use_shared =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check_nonlinear_select`,
       [use_shared;source_program;encoded_jobs]) in
  let run label use_shared =
    let current_call = call use_shared in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem =
      candle_q_dim_analytic_jet_compute
        candle_case10173_nonlinear_shared_compute_eqs current_call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    if not (candle_case10173_nonlinear_shared_validate current_call theorem)
    then failwith ("case10173 nonlinear-shared: " ^ label ^ " failed");
    theorem in
  let established_1 = run "established-1" `Cexp_num 0` in
  let shared_1 = run "shared-1" `Cexp_num 1` in
  let shared_2 = run "shared-2" `Cexp_num 1` in
  let established_2 = run "established-2" `Cexp_num 0` in
  let results = [established_1;shared_1;shared_2;established_2] in
  let first_result = rand (concl established_1) in
  let axioms_after = axioms () in
  if not (List.for_all (fun th -> aconv (rand (concl th)) first_result)
            results) ||
     hyp candle_cv_fso_program_step_nonlinear_shared_exact <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 nonlinear-shared: final validation failed";
  print_endline
    "CANDLE_CV_CASE10173_NONLINEAR_SHARED_PREFIX128_OK DEVELOPMENT_NON_RELEASE cells=128 established=2 shared=2 accepted=1 step_exact=1 assumptions=0 axiom_growth=0";;

end;;
