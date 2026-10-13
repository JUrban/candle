(* ========================================================================== *)
(* Case-10173 historical splice: logical contracts for complete job batches. *)
(*                                                                            *)
(* Numerical certificates and auxiliary roots remain ordinary data.  The    *)
(* source contract records the single structural fact needed for each pair   *)
(* of certificate-patched programs: replacing instructions 31--38 by the     *)
(* proved historical operation leaves an ordinary analytic context whose    *)
(* erased expression is the authenticated Flyspeck source.                    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_context_certified_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_variable_batch_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_certificate_patch;;
open Candle_cv_analytic_expr_certificate_patch_exact;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_stable_batch;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_context_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;

(* A logical root record has four fixed-scale intervals.  Pairing the first
   two and last two keeps the record shape fixed in the logic while this
   encoder reproduces the exact four-element cval list consumed by the
   executable checker. *)

let candle_cv_case10173_hist_root_records_def = define
 `(candle_cv_case10173_hist_root_records [] = Cexp_num 0) /\
  (candle_cv_case10173_hist_root_records (CONS record records) =
     Cexp_pair
       (candle_cv_fs_interval_list
         [FST (FST record); SND (FST record);
          FST (SND record); SND (SND record)])
       (candle_cv_case10173_hist_root_records records))`;;

(* This contract is deliberately structural rather than numerical.  The
   executable checker separately authenticates exact sqrt payloads, roots,
   guards, and the Taylor verdict. *)

let candle_case10173_hist_job_source_contract_def = new_definition
 `candle_case10173_hist_job_source_contract source_e job <=>
    let box_patched =
      SND (candle_analytic_patch_sqrt_certificates (FST job) source_e) in
    let center_patched =
      SND
        (candle_analytic_patch_sqrt_certificates
          (FST (SND job)) source_e) in
    ?context center_factor box_factor
       (box_lp:num) (box_ln:num) (box_ld:num)
       (box_up:num) (box_un:num) (box_ud:num).
      candle_case10173_hist_context_valid 6 context /\
      candle_analytic_valid_dim 6 box_factor /\
      candle_analytic_erase_sqrt_certificates center_factor =
        candle_analytic_erase_sqrt_certificates box_factor /\
      LENGTH (SND (SND job)) = 6 /\
      candle_q_box_valid_list (SND (SND job)) /\
      candle_cv_case10173_hist_splice_aux (Cexp_num 31)
        (candle_cv_analytic_instruction_list
          (candle_analytic_compile center_patched)) =
        candle_cv_case10173_hist_program_of
          (candle_case10173_hist_context_center_prefix context)
          (candle_case10173_hist_context_center_suffix
            context center_factor) /\
      candle_cv_case10173_hist_splice_aux (Cexp_num 31)
        (candle_cv_analytic_instruction_list
          (candle_analytic_compile box_patched)) =
        candle_cv_case10173_hist_program_of
          (candle_case10173_hist_context_box_prefix context)
          (candle_case10173_hist_context_box_suffix context box_factor) /\
      candle_analytic_erase_sqrt_certificates source_e =
        candle_analytic_erase_sqrt_certificates
          (candle_case10173_hist_context_box_expr context
            (candle_case10173_hist_source_dihedral_expr
              box_lp box_ln box_ld box_up box_un box_ud)
            box_factor)`;;

let candle_case10173_hist_jobs_source_contract_def = define
 `(candle_case10173_hist_jobs_source_contract source_e [] <=> T) /\
  (candle_case10173_hist_jobs_source_contract source_e (CONS job jobs) <=>
     candle_case10173_hist_job_source_contract source_e job /\
     candle_case10173_hist_jobs_source_contract source_e jobs)`;;

(* The only proposition exported from the numerical lane to topology is one
   source-level cell theorem per authenticated job. *)

let candle_case10173_hist_jobs_pass_def = define
 `(candle_case10173_hist_jobs_pass source_e [] <=> T) /\
  (candle_case10173_hist_jobs_pass source_e
      (CONS
        (job:
          (((num#num)#num)#((num#num)#num))list #
          ((((num#num)#num)#((num#num)#num))list #
           (((num#num)#num)#((num#num)#num))list))
        jobs) <=>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector (SND (SND job)):real^6),
        candle_q_box_upper_vector (SND (SND job))) /\
     candle_case10173_hist_jobs_pass source_e jobs)`;;

let candle_case10173_hist_jobs_source_contract_append = prove
 (`!left right source_e.
     candle_case10173_hist_jobs_source_contract source_e
       (APPEND left right) <=>
     candle_case10173_hist_jobs_source_contract source_e left /\
     candle_case10173_hist_jobs_source_contract source_e right`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND;candle_case10173_hist_jobs_source_contract_def] THEN
  MESON_TAC[]);;

let candle_case10173_hist_jobs_pass_append = prove
 (`!left right source_e.
     candle_case10173_hist_jobs_pass source_e (APPEND left right) <=>
     candle_case10173_hist_jobs_pass source_e left /\
     candle_case10173_hist_jobs_pass source_e right`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND;candle_case10173_hist_jobs_pass_def] THEN
  MESON_TAC[]);;

(* If a cval conditional with a false branch of zero accepted, its guard was
   truthy and its selected continuation accepted.  Keeping this small
   destructor separate avoids giving the batch proof any extra semantic view
   of the executable checker. *)

let candle_cv_case10173_hist_if_accept_elim = prove
  (`!guard consequent.
     Cexp_if guard consequent (Cexp_num 0) = Cexp_num 1
     ==>
     Cexp_if guard (Cexp_num 1) (Cexp_num 0) = Cexp_num 1 /\
     consequent = Cexp_num 1`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `guard:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    REWRITE_TAC[cexp_if_def;ONE;NOT_SUC;
                distinctness "cval";injectivity "cval"];
    REWRITE_TAC[cexp_if_def;ONE;NOT_SUC;
                distinctness "cval";injectivity "cval"]]);;

(* Complete checked-batch soundness.  The executable result is destructed one
   job at a time.  Each accepted head is discharged by the contextual source
   theorem above; the induction hypothesis handles the authenticated tail. *)

let candle_case10173_hist_checked_jobs_source_sound = prove
 (`!jobs roots source_e.
     candle_case10173_hist_jobs_source_contract source_e jobs /\
     candle_cv_case10173_hist_checked_jobs_check
       (candle_cv_analytic_instruction_list
         (candle_analytic_compile source_e))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs)
       (candle_cv_case10173_hist_root_records roots) = Cexp_num 1
     ==>
     candle_case10173_hist_jobs_pass source_e jobs`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_case10173_hist_jobs_pass_def];
    POP_ASSUM (LABEL_TAC "tail_sound") THEN
    X_GEN_TAC
      `root_records:
        ((((num#num)#(num#num))#((num#num)#(num#num)))#
         (((num#num)#(num#num))#((num#num)#(num#num))))list` THEN
    DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN
        `root_record:
          (((num#num)#(num#num))#((num#num)#(num#num)))#
          (((num#num)#(num#num))#((num#num)#(num#num)))`
        (X_CHOOSE_THEN
          `remaining_roots:
            ((((num#num)#(num#num))#((num#num)#(num#num)))#
             (((num#num)#(num#num))#((num#num)#(num#num))))list`
          SUBST1_TAC))
      (ISPEC
        `root_records:
          ((((num#num)#(num#num))#((num#num)#(num#num)))#
           (((num#num)#(num#num))#((num#num)#(num#num))))list`
        list_CASES) THENL
     [X_GEN_TAC `source_e:candle_analytic_expr` THEN
      REWRITE_TAC
        [candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
         candle_cv_case10173_hist_root_records_def;
         candle_cv_case10173_hist_checked_jobs_check_def;
         cexp_fst_def;cexp_snd_def;cexp_if_def;
         ONE;NOT_SUC;distinctness "cval";injectivity "cval"];
      ALL_TAC] THEN
    X_GEN_TAC `source_e:candle_analytic_expr` THEN
    REWRITE_TAC
      [candle_case10173_hist_jobs_source_contract_def;
       candle_case10173_hist_jobs_pass_def] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2
          (LABEL_TAC "head_contract")
          (LABEL_TAC "tail_contract"))
        (LABEL_TAC "checker_accept")) THEN
    USE_THEN "checker_accept" MP_TAC THEN
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
       candle_cv_case10173_hist_root_records_def;
       candle_cv_case10173_hist_checked_jobs_check_def;
       candle_cv_case10173_hist_root_record_check_correct;
       candle_cv_case10173_hist_production_guard_correct;
       candle_cv_analytic_program_sqrt_data_exact_correct;
       candle_cv_analytic_compile_patch_sqrt_correct;
       candle_cv_bool_def;
       cexp_fst_def;cexp_snd_def;LET_DEF;LET_END_DEF] THEN
    REPEAT
      (COND_CASES_TAC THEN
       ASM_REWRITE_TAC[cexp_if_def;injectivity "cval"] THEN
       TRY ARITH_TAC) THEN
    DISCH_THEN (MP_TAC o MATCH_MP
      candle_cv_case10173_hist_if_accept_elim) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2
        (LABEL_TAC "head_flag")
        (LABEL_TAC "tail_accept")) THEN
    CONJ_TAC THENL
     [REMOVE_THEN "head_contract" MP_TAC THEN
      REWRITE_TAC[candle_case10173_hist_job_source_contract_def;
                  LET_DEF;LET_END_DEF] THEN
      ASM_MESON_TAC
        [candle_case10173_hist_checked_context_source_cell_flag_sound];
      REMOVE_THEN "tail_sound"
        (MP_TAC o SPECL
          [`remaining_roots:
             ((((num#num)#(num#num))#((num#num)#(num#num)))#
              (((num#num)#(num#num))#((num#num)#(num#num))))list`;
           `source_e:candle_analytic_expr`]) THEN
      ASM_REWRITE_TAC[]]]);;

end;;
