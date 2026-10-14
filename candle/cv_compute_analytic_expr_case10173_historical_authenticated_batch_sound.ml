(* ========================================================================== *)
(* Genuine case-10173: reusable source contracts for complete job batches.   *)
(*                                                                            *)
(* Numerical acceptance is deliberately separate.  This predicate records   *)
(* only the exact source-patch widths and the six-dimensional box conditions *)
(* needed to instantiate the authenticated source contract once per job.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_source_contract.ml";;

module Candle_cv_analytic_expr_case10173_historical_authenticated_batch_sound = struct

open Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_source_contract;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;

let candle_case10173_hist_jobs_well_formed_def = define
 `(candle_case10173_hist_jobs_well_formed [] <=> T) /\
  (candle_case10173_hist_jobs_well_formed (CONS job jobs) <=>
     LENGTH (FST job) = 7 /\
     LENGTH (FST (SND job)) = 7 /\
     LENGTH (SND (SND job)) = 6 /\
     candle_q_box_valid_list (SND (SND job)) /\
     candle_case10173_hist_jobs_well_formed jobs)`;;

let candle_case10173_hist_length_seven = prove
 (`!items:A list.
     LENGTH items = 7 <=>
     ?x0 x1 x2 x3 x4 x5 x6.
       items = [x0;x1;x2;x3;x4;x5;x6]`,
  GEN_TAC THEN
  REWRITE_TAC
    [ARITH_RULE
      `7 = SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))`;
     LENGTH_EQ_CONS;LENGTH_EQ_NIL] THEN
  MESON_TAC[]);;

let candle_case10173_hist_jobs_well_formed_source_contract = prove
 (`!jobs.
     candle_case10173_hist_jobs_well_formed jobs
     ==>
     candle_case10173_hist_jobs_source_contract
       candle_case10173_hist_authenticated_source jobs`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [candle_case10173_hist_jobs_well_formed_def;
       candle_case10173_hist_jobs_source_contract_def];
    POP_ASSUM (LABEL_TAC "tail_contract") THEN
    X_CHOOSE_THEN
      `box_roots:(((num#num)#num)#((num#num)#num))list`
      (X_CHOOSE_THEN
        `center_and_box:
          (((num#num)#num)#((num#num)#num))list #
          (((num#num)#num)#((num#num)#num))list`
        SUBST1_TAC)
      (ISPEC
        `h:
          (((num#num)#num)#((num#num)#num))list #
          ((((num#num)#num)#((num#num)#num))list #
           (((num#num)#num)#((num#num)#num))list)`
        PAIR_SURJECTIVE) THEN
    X_CHOOSE_THEN
      `center_roots:(((num#num)#num)#((num#num)#num))list`
      (X_CHOOSE_THEN
        `boxes:(((num#num)#num)#((num#num)#num))list`
        SUBST1_TAC)
      (ISPEC
        `center_and_box:
          (((num#num)#num)#((num#num)#num))list #
          (((num#num)#num)#((num#num)#num))list`
        PAIR_SURJECTIVE) THEN
    REWRITE_TAC
      [candle_case10173_hist_jobs_well_formed_def;
       candle_case10173_hist_jobs_source_contract_def] THEN
    REWRITE_TAC[candle_case10173_hist_length_seven] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `b0:((num#num)#num)#((num#num)#num)`
          (X_CHOOSE_THEN `b1:((num#num)#num)#((num#num)#num)`
            (X_CHOOSE_THEN `b2:((num#num)#num)#((num#num)#num)`
              (X_CHOOSE_THEN `b3:((num#num)#num)#((num#num)#num)`
                (X_CHOOSE_THEN `b4:((num#num)#num)#((num#num)#num)`
                  (X_CHOOSE_THEN `b5:((num#num)#num)#((num#num)#num)`
                    (X_CHOOSE_THEN `b6:((num#num)#num)#((num#num)#num)`
                      SUBST_ALL_TAC)))))))
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `c0:((num#num)#num)#((num#num)#num)`
            (X_CHOOSE_THEN `c1:((num#num)#num)#((num#num)#num)`
              (X_CHOOSE_THEN `c2:((num#num)#num)#((num#num)#num)`
                (X_CHOOSE_THEN `c3:((num#num)#num)#((num#num)#num)`
                  (X_CHOOSE_THEN `c4:((num#num)#num)#((num#num)#num)`
                    (X_CHOOSE_THEN `c5:((num#num)#num)#((num#num)#num)`
                      (X_CHOOSE_THEN `c6:((num#num)#num)#((num#num)#num)`
                        SUBST_ALL_TAC)))))))
          STRIP_ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_case10173_hist_authenticated_job_source_contract THEN
      ASM_REWRITE_TAC[FST;SND];
      REMOVE_THEN "tail_contract" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE source-contract";;

(* The executable companion works over the existing canonical raw-job
   representation.  It deliberately checks only the cheap structural facts;
   the historical numerical checker remains the authority for arithmetic. *)

let candle_cv_case10173_hist_job_well_formed_def = new_definition
 `candle_cv_case10173_hist_job_well_formed job =
    candle_cv_bool_and
      (Cexp_eq (candle_cv_list_length (Cexp_fst job)) (Cexp_num 7))
      (candle_cv_bool_and
        (Cexp_eq
          (candle_cv_list_length (Cexp_fst (Cexp_snd job)))
          (Cexp_num 7))
        (candle_cv_bool_and
          (Cexp_eq
            (candle_cv_list_length (Cexp_snd (Cexp_snd job)))
            (Cexp_num 6))
          (candle_cv_q_box_valid_list (Cexp_snd (Cexp_snd job)))))`;;

let candle_cv_case10173_hist_jobs_well_formed_def = define
 `(candle_cv_case10173_hist_jobs_well_formed (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_case10173_hist_jobs_well_formed (Cexp_pair job jobs) =
     candle_cv_bool_and
       (candle_cv_case10173_hist_job_well_formed job)
       (candle_cv_case10173_hist_jobs_well_formed jobs))`;;

let candle_cv_case10173_hist_job_well_formed_correct = prove
 (`!job.
     candle_cv_case10173_hist_job_well_formed
       (Cexp_pair
         (candle_cv_q_interval_list (FST job))
         (Cexp_pair
           (candle_cv_q_interval_list (FST (SND job)))
           (candle_cv_q_interval_list (SND (SND job))))) =
     candle_cv_bool
       (LENGTH (FST job) = 7 /\
        LENGTH (FST (SND job)) = 7 /\
        LENGTH (SND (SND job)) = 6 /\
        candle_q_box_valid_list (SND (SND job)))`,
  GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_job_well_formed_def;
     cexp_fst_def;cexp_snd_def;
     candle_cv_interval_list_length_correct;
     candle_cv_q_box_valid_list_correct;
     cexp_eq_def;candle_cv_bool_and_correct;candle_cv_bool_def;
     injectivity "cval";injectivity "num";FST;SND] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  REWRITE_TAC[candle_cv_bool_and_def;cexp_if_def] THEN
  CONV_TAC NUM_REDUCE_CONV);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE job-well-formed";;

let candle_cv_case10173_hist_jobs_well_formed_correct = prove
 (`!jobs.
     candle_cv_case10173_hist_jobs_well_formed
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
     candle_cv_bool (candle_case10173_hist_jobs_well_formed jobs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC
    [candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
     candle_cv_case10173_hist_jobs_well_formed_def;
     candle_case10173_hist_jobs_well_formed_def;
     candle_cv_case10173_hist_job_well_formed_correct;
     candle_cv_bool_and_correct;
     cexp_eq_def;injectivity "cval";FST;SND] THEN
  REWRITE_TAC[candle_cv_bool_def] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  CONV_TAC NUM_REDUCE_CONV);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE jobs-well-formed";;

let candle_cv_case10173_hist_raw_jobs_well_formed_accept = prove
 (`!encoded.
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
       (candle_cv_fso_variable_jobs_decode encoded) = encoded /\
     candle_cv_case10173_hist_jobs_well_formed encoded = Cexp_num 1
     ==>
     candle_case10173_hist_jobs_well_formed
       (candle_cv_fso_variable_jobs_decode encoded)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (SPEC `candle_cv_fso_variable_jobs_decode encoded`
      candle_cv_case10173_hist_jobs_well_formed_correct) THEN
  ASM_REWRITE_TAC[candle_cv_bool_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE raw-jobs-well-formed";;

let candle_cv_case10173_hist_jobs_well_formed_compute = prove
 (`!encoded.
     candle_cv_case10173_hist_jobs_well_formed encoded =
     Cexp_if (Cexp_ispair encoded)
       (candle_cv_bool_and
         (candle_cv_case10173_hist_job_well_formed (Cexp_fst encoded))
         (candle_cv_case10173_hist_jobs_well_formed (Cexp_snd encoded)))
       (Cexp_eq encoded (Cexp_num 0))`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `encoded:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_case10173_hist_jobs_well_formed_def;
     cexp_if_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE compute";;

let candle_cv_case10173_hist_jobs_well_formed_compute_eqs =
  map SPEC_ALL
    [candle_cv_case10173_hist_job_well_formed_def;
     candle_cv_case10173_hist_jobs_well_formed_compute;
     candle_cv_list_length_compute;
     candle_cv_q_box_valid_list_compute;
     candle_cv_bool_and_def];;

let candle_case10173_hist_authenticated_checked_jobs_sound = prove
 (`!jobs roots.
     candle_case10173_hist_jobs_well_formed jobs /\
     candle_cv_case10173_hist_checked_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           candle_case10173_hist_authenticated_source))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs)
       (candle_cv_case10173_hist_root_records roots) = Cexp_num 1
     ==>
     candle_case10173_hist_jobs_pass
       candle_case10173_hist_authenticated_source jobs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_case10173_hist_checked_jobs_source_sound THEN
  EXISTS_TAC
    `roots:
      (((((num#num)#(num#num))#((num#num)#(num#num)))#
        (((num#num)#(num#num))#((num#num)#(num#num)))))list` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_case10173_hist_jobs_well_formed_source_contract THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE checked-jobs";;

let candle_case10173_hist_authenticated_checked_raw_jobs_sound = prove
 (`!encoded roots.
     candle_cv_case10173_hist_jobs_well_formed encoded = Cexp_num 1 /\
     candle_cv_case10173_hist_checked_raw_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile
           candle_case10173_hist_authenticated_source))
       encoded (candle_cv_case10173_hist_root_records roots) = Cexp_num 1
     ==>
     candle_case10173_hist_jobs_pass
       candle_case10173_hist_authenticated_source
       (candle_cv_fso_variable_jobs_decode encoded)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "well_formed")
      (LABEL_TAC "checked")) THEN
  REMOVE_THEN "checked"
    (MP_TAC o MATCH_MP
      (SPECL
        [`candle_cv_analytic_instruction_list
            (candle_analytic_compile
              candle_case10173_hist_authenticated_source)`;
         `encoded:cval`;
         `candle_cv_case10173_hist_root_records roots`]
        candle_cv_case10173_hist_checked_raw_jobs_accept)) THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
      (LABEL_TAC "representation")
      (LABEL_TAC "numerical")) THEN
  MATCH_MP_TAC candle_case10173_hist_authenticated_checked_jobs_sound THEN
  EXISTS_TAC
    `roots:
      (((((num#num)#(num#num))#((num#num)#(num#num)))#
        (((num#num)#(num#num))#((num#num)#(num#num)))))list` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_cv_case10173_hist_raw_jobs_well_formed_accept THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

print_endline "CANDLE_CASE10173_AUTH_BATCH_PHASE checked-raw-jobs";;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_AUTHENTICATED_BATCH_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
