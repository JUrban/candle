(* ========================================================================== *)
(* Lockstep semantic success for the packed-object whole-call boundary.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Each accepted reflected job is connected to a *)
(* genuine [m_cell_pass] fact for one common certificate-erased source.       *)
(* The common source is fixed by one authenticated reference replay; the      *)
(* source-identity theorem proves that all other accepted replays denote it.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_object_identity_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_dispatch_entry_success_sound.ml";;
needs "candle/cv_compute_analytic_expr_packed_source_object_whole_skeleton_sound.ml";;

module Candle_cv_analytic_expr_packed_source_object_whole_success_sound = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_sound;;
open Candle_cv_analytic_expr_packed_source_certificate_dispatch_entry_sound;;
open Candle_cv_analytic_expr_packed_source_object_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_complete_program_sound;;
open Candle_cv_analytic_expr_packed_source_object_identity_sound;;
open Candle_cv_analytic_expr_packed_source_object_dispatch_entry_success_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_packed_source_object_whole_compute;;
open Candle_cv_analytic_expr_packed_source_object_whole_skeleton_sound;;

let candle_cv_q_packed_object_whole_job_accept_cell_pass = prove
 (`!codes sources reference_center_boxes reference_outer_boxes reference_radii
      reference_certificates reference_item reference_certificate_rest
      source_boxes center_boxes outer_boxes radii certificates.
     candle_q_packed_object_source_planned_program_run reference_center_boxes
       reference_outer_boxes reference_radii codes sources
       reference_certificates [] [reference_item]
       reference_certificate_rest /\
     LENGTH source_boxes = 6 /\ LENGTH center_boxes = 6 /\
     LENGTH outer_boxes = 6 /\ LENGTH radii = 6 /\
     candle_q_packed_source_correspondence
       source_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_correspondence
       outer_boxes center_boxes outer_boxes radii /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_cv_q_packed_object_whole_job_check
       (candle_cv_q_packed_object_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (Cexp_pair (candle_cv_q_list radii)
         (candle_cv_q_interval_list certificates))
       (Cexp_pair (candle_cv_q_interval_list outer_boxes)
         (Cexp_pair (candle_cv_q_interval_list center_boxes)
           (candle_cv_q_interval_list source_boxes))) = Cexp_num 1
     ==>
     m_cell_pass
       (candle_analytic_denote_dim
         (candle_analytic_erase_sqrt_certificates
           (candle_q_packed_object_item_box_expr reference_item)))
       ((candle_q_box_lower_vector source_boxes:real^6),
        (candle_q_box_upper_vector source_boxes:real^6))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [candle_cv_q_packed_object_whole_job_check_def;
     LET_DEF; LET_END_DEF; cexp_fst_def; cexp_snd_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "reference_run")
      (CONJUNCTS_THEN2 (LABEL_TAC "source_length")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_length")
          (CONJUNCTS_THEN2 (LABEL_TAC "outer_length")
            (CONJUNCTS_THEN2 (LABEL_TAC "radii_length")
              (CONJUNCTS_THEN2 (LABEL_TAC "source_correspondence")
                (CONJUNCTS_THEN2 (LABEL_TAC "outer_correspondence")
                  (CONJUNCTS_THEN2 (LABEL_TAC "planned_program")
                    (LABEL_TAC "entry_accept"))))))))) THEN
  MP_TAC
    (MATCH_MP
      (SPECL
        [`source_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
         `radii:((num#num)#num)list`; `codes:num list`;
         `sources:candle_analytic_instruction list`;
         `certificates:(((num#num)#num)#((num#num)#num))list`]
        candle_cv_q_packed_object_dispatch_entry_accept_cell_pass)
      (end_itlist CONJ
        [ASSUME `LENGTH
          (source_boxes:((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME `LENGTH
          (center_boxes:((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME `LENGTH
          (outer_boxes:((((num#num)#num)#((num#num)#num))list)) = 6`;
         ASSUME `LENGTH (radii:((num#num)#num)list) = 6`;
         ASSUME
          `candle_q_packed_source_correspondence source_boxes center_boxes
            outer_boxes radii`;
         ASSUME
          `candle_q_packed_source_correspondence outer_boxes center_boxes
            outer_boxes radii`;
         ASSUME
          `candle_q_packed_source_planned_program_instructions codes sources`;
         ASSUME
          `candle_cv_q_packed_object_dispatch_entry
            (candle_cv_q_interval_list center_boxes)
            (candle_cv_q_interval_list outer_boxes)
            (candle_cv_q_list radii)
            (candle_cv_q_packed_object_plan_code_list codes)
            (candle_cv_analytic_instruction_list sources)
            (candle_cv_q_interval_list certificates) = Cexp_num 1`])) THEN
  DISCH_THEN
    (REPEAT_TCL CHOOSE_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "job_run")
        (LABEL_TAC "job_pass"))) THEN
  SUBGOAL_THEN
   `candle_analytic_erase_sqrt_certificates
      (candle_q_packed_object_item_box_expr reference_item) =
    candle_analytic_erase_sqrt_certificates box_e`
  (LABEL_TAC "source_identity") THENL
   [MP_TAC
      (MATCH_MP
        (SPECL
          [`codes:num list`; `sources:candle_analytic_instruction list`;
           `reference_center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `reference_outer_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `reference_radii:((num#num)#num)list`;
           `radii:((num#num)#num)list`;
           `reference_certificates:
             (((num#num)#num)#((num#num)#num))list`;
           `certificates:(((num#num)#num)#((num#num)#num))list`;
           `reference_item:candle_q_packed_object_item`;
           `Candle_q_packed_object_item
             (Candle_q_packed_object_state domain center_value center_gradient
               value_bound gradient_bounds packed_hessian) center_e box_e`;
           `reference_certificate_rest:
             (((num#num)#num)#((num#num)#num))list`;
           `[]:(((num#num)#num)#((num#num)#num))list`]
          candle_q_packed_object_planned_singleton_expr_equal)
        (CONJ
          (ASSUME
            `candle_q_packed_object_source_planned_program_run
              reference_center_boxes reference_outer_boxes reference_radii
              codes sources reference_certificates [] [reference_item]
              reference_certificate_rest`)
          (ASSUME
            `candle_q_packed_object_source_planned_program_run center_boxes
              outer_boxes radii codes sources certificates []
              [Candle_q_packed_object_item
                (Candle_q_packed_object_state domain center_value
                  center_gradient value_bound gradient_bounds packed_hessian)
                center_e box_e] []`))) THEN
    REWRITE_TAC[candle_q_packed_object_item_box_expr_def];
    SUBGOAL_THEN
     `(candle_analytic_denote_dim
        (candle_analytic_erase_sqrt_certificates
          (candle_q_packed_object_item_box_expr reference_item)):
        real^6->real) =
      candle_analytic_denote_dim box_e`
    (fun source_denote -> ASM_REWRITE_TAC[source_denote]) THEN
    ASM_MESON_TAC
      [candle_analytic_erase_denote_dim;
       candle_analytic_denote_certificate_transport]]);;

if hyp candle_cv_q_packed_object_whole_job_accept_cell_pass <> [] then
  failwith "packed object whole success: job assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_JOB_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

let candle_cv_q_packed_object_cells_def = define
 `(candle_cv_q_packed_object_cells [] = Cexp_num 0) /\
  (candle_cv_q_packed_object_cells (CONS packed_cell packed_cells) =
     Cexp_pair
       (Cexp_pair (candle_cv_q_list (FST packed_cell))
         (candle_cv_q_interval_list (SND packed_cell)))
       (candle_cv_q_packed_object_cells packed_cells))`;;

let candle_q_packed_object_whole_input_contract_def = define
 `(candle_q_packed_object_whole_input_contract [] [] <=> T) /\
  (candle_q_packed_object_whole_input_contract [] (CONS job jobs) <=> F) /\
  (candle_q_packed_object_whole_input_contract
      (CONS packed_cell packed_cells) [] <=> F) /\
  (candle_q_packed_object_whole_input_contract
      (CONS packed_cell packed_cells) (CONS job jobs) <=>
     LENGTH (SND (SND job)) = 6 /\
     LENGTH (FST (SND job)) = 6 /\
     LENGTH (FST job) = 6 /\
     LENGTH (FST packed_cell) = 6 /\
     candle_q_packed_source_correspondence
       (SND (SND job)) (FST (SND job)) (FST job) (FST packed_cell) /\
     candle_q_packed_source_correspondence
       (FST job) (FST (SND job)) (FST job) (FST packed_cell) /\
     candle_q_packed_object_whole_input_contract packed_cells jobs)`;;

let candle_cv_q_packed_object_whole_jobs_accept_goal =
 `!packed_cells jobs codes sources reference_center_boxes
      reference_outer_boxes reference_radii reference_certificates
      reference_item reference_certificate_rest (type_witness:real^6).
     candle_cv_q_packed_object_whole_jobs_check
       (candle_cv_q_packed_object_plan_code_list codes)
       (candle_cv_analytic_instruction_list sources)
       (candle_cv_q_packed_object_cells packed_cells)
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
       Cexp_num 1 /\
     candle_q_packed_object_whole_input_contract packed_cells jobs /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_q_packed_object_source_planned_program_run reference_center_boxes
       reference_outer_boxes reference_radii codes sources
       reference_certificates [] [reference_item]
       reference_certificate_rest
     ==>
     candle_q_packed_object_whole_jobs_pass type_witness
       (candle_analytic_erase_sqrt_certificates
         (candle_q_packed_object_item_box_expr reference_item)) jobs`;;
let candle_cv_q_packed_object_whole_jobs_accept = prove
 (candle_cv_q_packed_object_whole_jobs_accept_goal,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_cv_q_packed_object_cells_def;
         candle_q_packed_object_whole_input_contract_def;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
         candle_cv_q_packed_object_whole_jobs_check_def;
         candle_q_packed_object_whole_jobs_pass_def;
         candle_cv_bool_and_def; candle_cv_bool_def;
         cexp_eq_def; cexp_if_def; injectivity "cval"] THEN
      CONV_TAC NUM_REDUCE_CONV;
      REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_q_packed_object_whole_input_contract_def]];
    POP_ASSUM (LABEL_TAC "induction_hypothesis") THEN
    LIST_INDUCT_TAC THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC[candle_q_packed_object_whole_input_contract_def];
      X_CHOOSE_THEN `radii:((num#num)#num)list`
        (X_CHOOSE_THEN
          `certificates:(((num#num)#num)#((num#num)#num))list`
          SUBST1_TAC)
        (ISPEC
          `h:((num#num)#num)list #
             (((num#num)#num)#((num#num)#num))list`
          PAIR_SURJECTIVE) THEN
      X_CHOOSE_THEN
        `outer_boxes:(((num#num)#num)#((num#num)#num))list`
        (X_CHOOSE_THEN
          `center_and_source:
            (((num#num)#num)#((num#num)#num))list #
            (((num#num)#num)#((num#num)#num))list`
          SUBST1_TAC)
        (ISPEC
          `h':
            (((num#num)#num)#((num#num)#num))list #
            ((((num#num)#num)#((num#num)#num))list #
             (((num#num)#num)#((num#num)#num))list)`
          PAIR_SURJECTIVE) THEN
      X_CHOOSE_THEN
        `center_boxes:(((num#num)#num)#((num#num)#num))list`
        (X_CHOOSE_THEN
          `source_boxes:(((num#num)#num)#((num#num)#num))list`
          SUBST1_TAC)
        (ISPEC
          `center_and_source:
            (((num#num)#num)#((num#num)#num))list #
            (((num#num)#num)#((num#num)#num))list`
          PAIR_SURJECTIVE) THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_cv_q_packed_object_cells_def;
         candle_q_packed_object_whole_input_contract_def;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
         candle_cv_q_packed_object_whole_jobs_check_def;
         candle_q_packed_object_whole_jobs_pass_def;
         LET_DEF; LET_END_DEF; FST; SND;
         cexp_fst_def; cexp_snd_def;
         candle_cv_bool_and_def; candle_cv_equal_correct;
         candle_cv_guarded_accept_one] THEN
      STRIP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC candle_cv_q_packed_object_whole_job_accept_cell_pass THEN
        MAP_EVERY EXISTS_TAC
          [`codes:num list`; `sources:candle_analytic_instruction list`;
           `reference_center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `reference_outer_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `reference_radii:((num#num)#num)list`;
           `reference_certificates:
             (((num#num)#num)#((num#num)#num))list`;
           `reference_certificate_rest:
             (((num#num)#num)#((num#num)#num))list`;
           `center_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `outer_boxes:((((num#num)#num)#((num#num)#num))list)`;
           `radii:((num#num)#num)list`;
           `certificates:(((num#num)#num)#((num#num)#num))list`] THEN
        ASM_REWRITE_TAC[];
        USE_THEN "induction_hypothesis" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC
          [`codes:num list`; `sources:candle_analytic_instruction list`;
           `reference_center_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `reference_outer_boxes:
             ((((num#num)#num)#((num#num)#num))list)`;
           `reference_radii:((num#num)#num)list`;
           `reference_certificates:
             (((num#num)#num)#((num#num)#num))list`;
           `reference_certificate_rest:
             (((num#num)#num)#((num#num)#num))list`] THEN
        ASM_REWRITE_TAC[]]]]);;

if hyp candle_cv_q_packed_object_whole_jobs_accept <> [] then
  failwith "packed object whole success: jobs assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_JOBS_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

let candle_cv_q_packed_object_whole_success = prove
 (`!packed_cells jobs codes sources reference_center_boxes
      reference_outer_boxes reference_radii reference_certificates
      reference_item reference_certificate_rest (type_witness:real^6)
      tokens encoded_root.
     candle_q_packed_object_whole_input_contract packed_cells jobs /\
     candle_q_packed_source_planned_program_instructions codes sources /\
     candle_q_packed_object_source_planned_program_run reference_center_boxes
       reference_outer_boxes reference_radii codes sources
       reference_certificates [] [reference_item]
       reference_certificate_rest /\
     candle_cv_q_packed_object_whole_check
       (Cexp_pair (candle_cv_q_packed_object_plan_code_list codes)
         (Cexp_pair (candle_cv_analytic_instruction_list sources)
           (candle_cv_q_packed_object_cells packed_cells)))
       (Cexp_num (dimindex (:6)))
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
         tokens)
       (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
     Cexp_pair (Cexp_num 1)
       (Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0))))
     ==>
     m_cell_pass
       (candle_analytic_denote_dim
         (candle_analytic_erase_sqrt_certificates
           (candle_q_packed_object_item_box_expr reference_item)))
       ((candle_q_box_lower_vector
          (candle_cv_q_interval_list_decode encoded_root):real^6),
        (candle_q_box_upper_vector
          (candle_cv_q_interval_list_decode encoded_root):real^6))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2 (LABEL_TAC "input_contract")
      (CONJUNCTS_THEN2 (LABEL_TAC "planned_program")
        (CONJUNCTS_THEN2 (LABEL_TAC "reference_run")
          (LABEL_TAC "whole")))) THEN
  SUBGOAL_THEN
   `candle_cv_q_packed_object_whole_jobs_check
      (candle_cv_q_packed_object_plan_code_list codes)
      (candle_cv_analytic_instruction_list sources)
      (candle_cv_q_packed_object_cells packed_cells)
      (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
    Cexp_num 1`
  (LABEL_TAC "jobs_accepted") THENL
   [MP_TAC
      (MATCH_MP
        (SPEC_ALL candle_cv_q_packed_object_whole_components)
        (ASSUME
          `candle_cv_q_packed_object_whole_check
            (Cexp_pair (candle_cv_q_packed_object_plan_code_list codes)
              (Cexp_pair (candle_cv_analytic_instruction_list sources)
                (candle_cv_q_packed_object_cells packed_cells)))
            (Cexp_num (dimindex (:6)))
            (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
              tokens)
            (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs) =
          Cexp_pair (Cexp_num 1)
            (Cexp_pair (Cexp_num 1)
              (Cexp_pair (Cexp_num 0)
                (Cexp_pair encoded_root (Cexp_num 0))))`)) THEN
    REWRITE_TAC[cexp_fst_def; cexp_snd_def] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_packed_object_whole_jobs_pass (type_witness:real^6)
      (candle_analytic_erase_sqrt_certificates
        (candle_q_packed_object_item_box_expr reference_item)) jobs`
  (LABEL_TAC "jobs_pass") THENL
   [MATCH_MP_TAC (SPEC_ALL candle_cv_q_packed_object_whole_jobs_accept) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC
    (ISPECL
      [`candle_analytic_erase_sqrt_certificates
          (candle_q_packed_object_item_box_expr reference_item)`;
       `type_witness:real^6`;
       `Cexp_pair (candle_cv_q_packed_object_plan_code_list codes)
          (Cexp_pair (candle_cv_analytic_instruction_list sources)
            (candle_cv_q_packed_object_cells packed_cells))`;
       `tokens:
          candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
       `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs`;
       `encoded_root:cval`]
      candle_cv_q_packed_object_whole_accept) THEN
  ASM_REWRITE_TAC[candle_cv_fso_variable_jobs_decode_roundtrip]);;

if hyp candle_cv_q_packed_object_whole_success <> [] then
  failwith "packed object whole success: final assumptions";;

print_endline
  "CANDLE_CV_PACKED_OBJECT_WHOLE_SUCCESS_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
