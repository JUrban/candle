(* ========================================================================== *)
(* Fixed nonlinear dense-propagation discriminator on real case-10173 cells. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The candidate retains the *)
(* existing rational scalar enclosures but outward-rounds dense propagation  *)
(* to the established fixed scale.  Acceptance and timing are both measured. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_fixed_nonlinear_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_cv_fso_program_run_fixed_nonlinear_def = define
 `(candle_cv_fso_program_run_fixed_nonlinear
     center_boxes boxes radii (Cexp_num n) box_program stack = stack) /\
  (candle_cv_fso_program_run_fixed_nonlinear
     center_boxes boxes radii (Cexp_pair ch ct) (Cexp_num n) stack = stack) /\
  (candle_cv_fso_program_run_fixed_nonlinear
     center_boxes boxes radii
     (Cexp_pair ch ct) (Cexp_pair bh bt) stack =
     candle_cv_fso_program_run_fixed_nonlinear
       center_boxes boxes radii ct bt
       (candle_cv_fso_program_step_fixed_nonlinear
         center_boxes boxes radii ch bh stack))`;;

let candle_cv_fso_program_run_fixed_nonlinear_compute = prove
 (`!center_boxes boxes radii center_program box_program stack.
     candle_cv_fso_program_run_fixed_nonlinear
       center_boxes boxes radii center_program box_program stack =
     Cexp_if (Cexp_ispair center_program)
       (Cexp_if (Cexp_ispair box_program)
         (candle_cv_fso_program_run_fixed_nonlinear
           center_boxes boxes radii
           (Cexp_snd center_program) (Cexp_snd box_program)
           (candle_cv_fso_program_step_fixed_nonlinear
             center_boxes boxes radii
             (Cexp_fst center_program) (Cexp_fst box_program) stack))
         stack)
       stack`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `center_program:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `box_program:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_program_run_fixed_nonlinear_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fso_program_fixed_nonlinear_def = new_definition
 `candle_cv_fso_program_fixed_nonlinear center_program box_program boxes =
    candle_cv_fsa_item_to_q
      (candle_cv_fsa_item_head
        (candle_cv_q_center_environment_list boxes) boxes
        (candle_cv_fso_program_run_fixed_nonlinear
          (candle_cv_q_center_environment_list boxes) boxes
          (candle_cv_q_fixed_list_round_upper
            (candle_cv_q_radius_list boxes))
          center_program box_program (Cexp_num 0)))`;;

let candle_cv_fso_certified_check_fixed_nonlinear_def = new_definition
 `candle_cv_fso_certified_check_fixed_nonlinear
      center_program box_program boxes =
    candle_cv_q_dim_taylor_model_certified_finish boxes
      (candle_cv_fso_program_fixed_nonlinear
        center_program box_program boxes)`;;

let candle_cv_fso_variable_jobs_check_fixed_nonlinear_def = define
 `(candle_cv_fso_variable_jobs_check_fixed_nonlinear
      source_program (Cexp_num n) = Cexp_num 1) /\
  (candle_cv_fso_variable_jobs_check_fixed_nonlinear
      source_program (Cexp_pair job jobs) =
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
               (candle_cv_fso_certified_check_fixed_nonlinear
                 (Cexp_snd center_patched) (Cexp_snd box_patched)
                 (Cexp_snd (Cexp_snd job))))
             (candle_cv_fso_variable_jobs_check_fixed_nonlinear
               source_program jobs)
             (Cexp_num 0))
          (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_fso_variable_jobs_check_fixed_nonlinear_compute = prove
 (`!source_program jobs.
     candle_cv_fso_variable_jobs_check_fixed_nonlinear source_program jobs =
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
                 (candle_cv_fso_certified_check_fixed_nonlinear
                   (Cexp_snd center_patched) (Cexp_snd box_patched)
                   (Cexp_snd (Cexp_snd (Cexp_fst jobs)))))
               (candle_cv_fso_variable_jobs_check_fixed_nonlinear
                 source_program (Cexp_snd jobs))
               (Cexp_num 0))
            (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fso_variable_jobs_check_fixed_nonlinear_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
     LET_DEF;LET_END_DEF]);;

let candle_cv_fso_variable_raw_jobs_check_fixed_nonlinear_def =
  new_definition
   `candle_cv_fso_variable_raw_jobs_check_fixed_nonlinear
        source_program encoded_jobs =
      candle_cv_bool_and
        (Cexp_eq (candle_cv_fso_variable_jobs_canonical encoded_jobs)
          encoded_jobs)
        (candle_cv_fso_variable_jobs_check_fixed_nonlinear
          source_program encoded_jobs)`;;

let candle_case10173_fixed_nonlinear_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fso_variable_raw_compute_eqs
      (union candle_cv_fixed_nonlinear_compute_eqs
        (map SPEC_ALL
          [candle_cv_fso_program_run_fixed_nonlinear_compute;
           candle_cv_fso_program_fixed_nonlinear_def;
           candle_cv_fso_certified_check_fixed_nonlinear_def;
           candle_cv_fso_variable_jobs_check_fixed_nonlinear_compute;
           candle_cv_fso_variable_raw_jobs_check_fixed_nonlinear_def])));;

let rec candle_case10173_fixed_nonlinear_cval_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case10173 fixed-nonlinear prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_fixed_nonlinear_cval_take (count - 1) tail);;

let candle_case10173_fixed_nonlinear_validate expected call theorem =
  hyp theorem = [] && aconv (lhand (concl theorem)) call &&
  aconv (rand (concl theorem)) expected;;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=case10173-fixed-nonlinear-prefix128" ^
         " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let encoded_jobs =
    candle_case10173_fixed_nonlinear_cval_take 128
      captured.case10173_complete_encoded_jobs in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let established_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [source_program;encoded_jobs]) in
  let candidate_call =
    list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check_fixed_nonlinear`,
       [source_program;encoded_jobs]) in
  let run label equations call =
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem = candle_q_dim_analytic_jet_compute equations call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    theorem in
  let established_1 =
    run "established-1" candle_cv_fso_variable_raw_compute_eqs
      established_call in
  let candidate_1 =
    run "candidate-1" candle_case10173_fixed_nonlinear_compute_eqs
      candidate_call in
  let candidate_2 =
    run "candidate-2" candle_case10173_fixed_nonlinear_compute_eqs
      candidate_call in
  let established_2 =
    run "established-2" candle_cv_fso_variable_raw_compute_eqs
      established_call in
  if not
       (candle_case10173_fixed_nonlinear_validate
         `Cexp_num 1` established_call established_1) ||
     not
       (candle_case10173_fixed_nonlinear_validate
         `Cexp_num 1` established_call established_2) ||
     not (hyp candidate_1 = [] &&
          aconv (lhand (concl candidate_1)) candidate_call) ||
     not (hyp candidate_2 = [] &&
          aconv (lhand (concl candidate_2)) candidate_call) ||
     not (aconv (rand (concl candidate_1)) (rand (concl candidate_2))) ||
     length axioms_before <> length (axioms ()) ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 fixed-nonlinear: validation failed";
  print_endline
    ("CANDLE_CV_CASE10173_FIXED_NONLINEAR_PREFIX128_OK" ^
     " DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128" ^
     " established=2 candidate=2 established_result=1 candidate_result=" ^
     (if aconv (rand (concl candidate_1)) `Cexp_num 1` then "1" else "0") ^
     " assumptions=0 axiom_growth=0");;

end;;
