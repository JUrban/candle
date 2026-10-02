(* ========================================================================== *)
(* One-verdict reflected checker for a complete variable Taylor certificate.  *)
(*                                                                            *)
(* The numerical jobs and compact topology remain raw cval data throughout   *)
(* evaluation.  The computed result retains only the numerical verdict and   *)
(* the compact topology result.  A single general theorem recovers the        *)
(* logical job acceptance and root-cell theorem; callers need not construct   *)
(* or combine a concrete jobs_accept theorem.                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_complete_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_representation_support;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;

let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE components begin";;
let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_components =
  prove
   (`!source_program tree_dim tokens encoded_jobs encoded_root.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
         source_program tree_dim tokens encoded_jobs =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 1)
           (Cexp_pair (Cexp_num 0)
             (Cexp_pair encoded_root (Cexp_num 0))))
       ==>
       candle_cv_fso_variable_raw_jobs_check
         source_program encoded_jobs = Cexp_num 1 /\
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens encoded_jobs (Cexp_num 0) =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0)))`,
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_def;
       injectivity "cval"]);;
let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE components end";;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_stack_components =
  prove
   (`!source_program tree_dim tokens encoded_jobs encoded_stack.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
         source_program tree_dim tokens encoded_jobs =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 1)
           (Cexp_pair (Cexp_num 0) encoded_stack))
       ==>
       candle_cv_fso_variable_raw_jobs_check
         source_program encoded_jobs = Cexp_num 1 /\
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens encoded_jobs (Cexp_num 0) =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0) encoded_stack)`,
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check_def;
       injectivity "cval"]);;

let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE stack-accept begin";;
let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_stack_accept =
  prove
   (`!source_e (type_witness:real^N) tokens encoded_jobs encoded_stack.
       candle_analytic_valid_dim (dimindex (:N)) source_e /\
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
         (candle_cv_analytic_instruction_list
           (candle_analytic_compile source_e))
         (Cexp_num (dimindex (:N)))
         (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
           tokens)
         encoded_jobs =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 1)
           (Cexp_pair (Cexp_num 0) encoded_stack))
       ==>
       candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
         type_witness source_e
         (candle_cv_q_boxes_stack_decode encoded_stack)`,
    REPEAT GEN_TAC THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "valid") (LABEL_TAC "complete")) THEN
    USE_THEN "complete"
      (fun complete ->
        MP_TAC
          (MATCH_MP
            (SPECL
              [`candle_cv_analytic_instruction_list
                  (candle_analytic_compile source_e)`;
               `Cexp_num (dimindex (:N))`;
               `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
                  tokens`;
               `encoded_jobs:cval`;`encoded_stack:cval`]
              candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_stack_components)
            complete)) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "numerical") (LABEL_TAC "topology")) THEN
    SUBGOAL_THEN
     `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
        (candle_cv_fso_variable_jobs_decode encoded_jobs) = encoded_jobs`
      (LABEL_TAC "representation") THENL
     [USE_THEN "numerical"
        (fun numerical ->
          ACCEPT_TAC
            (MATCH_MP
              (SPECL
                [`encoded_jobs:cval`;`source_e:candle_analytic_expr`]
                candle_cv_fso_variable_raw_jobs_check_representation_accept)
              numerical));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
        source_e (candle_cv_fso_variable_jobs_decode encoded_jobs)`
      (LABEL_TAC "accepted") THENL
     [USE_THEN "numerical"
        (fun numerical ->
          ACCEPT_TAC
            (MATCH_MP
              (SPECL
                [`encoded_jobs:cval`;`source_e:candle_analytic_expr`]
                candle_cv_fso_variable_raw_jobs_check_accept)
              numerical));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_outer_variable_compact_run
        (dimindex (:N)) tokens
        (candle_cv_fso_variable_jobs_decode encoded_jobs) [] =
      (T,([],(candle_cv_q_boxes_stack_decode encoded_stack)))`
      (LABEL_TAC "logical_run") THENL
     [MP_TAC
        (SPECL
          [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
           `dimindex (:N)`;
           `candle_cv_fso_variable_jobs_decode encoded_jobs`;
           `[]:((((num#num)#num)#((num#num)#num))list)list`]
          candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct) THEN
      ASM_REWRITE_TAC[candle_cv_q_boxes_stack_def] THEN
      DISCH_THEN
        (fun correspondence ->
          MP_TAC
            (AP_TERM
              `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
              (SYM correspondence))) THEN
      REWRITE_TAC
        [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
         candle_cv_fso_variable_jobs_decode_def;
         cexp_fst_def;cexp_snd_def;injectivity "cval"];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass
        (type_witness:real^N) source_e []`
      ASSUME_TAC THENL
     [REWRITE_TAC
        [candle_q_dim_taylor_model_fixed_outer_variable_compact_stack_pass_def];
      ALL_TAC] THEN
    MP_TAC
      (ISPECL
        [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
         `source_e:candle_analytic_expr`;`type_witness:real^N`;
         `candle_cv_fso_variable_jobs_decode encoded_jobs`;
         `[]:((((num#num)#num)#((num#num)#num))list)list`;
         `[]:((((num#num)#num)#((num#num)#num))list#
            ((((num#num)#num)#((num#num)#num))list#
             (((num#num)#num)#((num#num)#num))list))list`;
         `candle_cv_q_boxes_stack_decode encoded_stack`]
        candle_q_dim_taylor_model_fixed_outer_variable_compact_run_sound) THEN
    ASM_MESON_TAC[]);;
let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE stack-accept end";;

let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE accept begin";;
let candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_accept =
  prove
   (`!source_e (type_witness:real^N) tokens encoded_jobs encoded_root.
       candle_analytic_valid_dim (dimindex (:N)) source_e /\
       candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_check
         (candle_cv_analytic_instruction_list
           (candle_analytic_compile source_e))
         (Cexp_num (dimindex (:N)))
         (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
           tokens)
         encoded_jobs =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 1)
           (Cexp_pair (Cexp_num 0)
             (Cexp_pair encoded_root (Cexp_num 0))))
       ==>
       m_cell_pass
         (candle_analytic_denote_dim source_e)
         ((candle_q_box_lower_vector
            (candle_cv_q_interval_list_decode encoded_root):real^N),
          (candle_q_box_upper_vector
            (candle_cv_q_interval_list_decode encoded_root):real^N))`,
    REPEAT GEN_TAC THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "valid") (LABEL_TAC "complete")) THEN
    USE_THEN "complete"
      (fun complete ->
        MP_TAC
          (MATCH_MP
            (SPECL
              [`candle_cv_analytic_instruction_list
                  (candle_analytic_compile source_e)`;
               `Cexp_num (dimindex (:N))`;
               `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
                  tokens`;
               `encoded_jobs:cval`;`encoded_root:cval`]
              candle_cv_q_dim_taylor_model_fixed_outer_variable_complete_components)
            complete)) THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "numerical") (LABEL_TAC "topology")) THEN
    SUBGOAL_THEN
     `candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
        (candle_cv_fso_variable_jobs_decode encoded_jobs) = encoded_jobs`
      (LABEL_TAC "representation") THENL
     [USE_THEN "numerical"
        (fun numerical ->
          ACCEPT_TAC
            (MATCH_MP
              (SPECL
                [`encoded_jobs:cval`;`source_e:candle_analytic_expr`]
                candle_cv_fso_variable_raw_jobs_check_representation_accept)
              numerical));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
        source_e (candle_cv_fso_variable_jobs_decode encoded_jobs)`
      (LABEL_TAC "accepted") THENL
     [USE_THEN "numerical"
        (fun numerical ->
          ACCEPT_TAC
            (MATCH_MP
              (SPECL
                [`encoded_jobs:cval`;`source_e:candle_analytic_expr`]
                candle_cv_fso_variable_raw_jobs_check_accept)
              numerical));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_outer_variable_compact_run
        (dimindex (:N)) tokens
        (candle_cv_fso_variable_jobs_decode encoded_jobs) [] =
      (T,([],[candle_cv_q_interval_list_decode encoded_root]))`
      (LABEL_TAC "logical_run") THENL
     [MP_TAC
        (SPECL
          [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
           `dimindex (:N)`;
           `candle_cv_fso_variable_jobs_decode encoded_jobs`;
           `[]:((((num#num)#num)#((num#num)#num))list)list`]
          candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct) THEN
      ASM_REWRITE_TAC[candle_cv_q_boxes_stack_def] THEN
      DISCH_THEN
        (fun correspondence ->
          MP_TAC
            (AP_TERM
              `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode`
              (SYM correspondence))) THEN
      REWRITE_TAC
        [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_roundtrip;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_decode_def;
         candle_cv_fso_variable_jobs_decode_def;
         candle_cv_q_boxes_stack_decode_def;
         cexp_fst_def;cexp_snd_def;injectivity "cval"];
      ALL_TAC] THEN
    USE_THEN "valid"
      (fun valid ->
        USE_THEN "accepted"
          (fun accepted ->
            USE_THEN "logical_run"
              (fun logical_run ->
                ACCEPT_TAC
                  (MATCH_MP
                    (ISPECL
                      [`source_e:candle_analytic_expr`;
                       `type_witness:real^N`;
                       `tokens:candle_q_dim_taylor_model_fixed_outer_variable_compact_token list`;
                       `candle_cv_fso_variable_jobs_decode encoded_jobs`;
                       `candle_cv_q_interval_list_decode encoded_root`]
                      candle_q_dim_taylor_model_fixed_outer_variable_compact_sound)
                    (CONJ valid (CONJ accepted logical_run)))))));;
let _ = print_endline "CANDLE_CV_COMPLETE_SOUND_PHASE accept end";;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPLETE_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
