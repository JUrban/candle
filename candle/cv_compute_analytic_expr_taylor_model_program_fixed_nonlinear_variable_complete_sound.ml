(* ========================================================================== *)
(* Soundness of the one-verdict fixed-nonlinear complete checker.             *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_raw_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_variable_complete_compute;;

let candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_components =
  prove
   (`!source_program tree_dim tokens encoded_jobs encoded_root.
       candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check
         source_program tree_dim tokens encoded_jobs =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 1)
           (Cexp_pair (Cexp_num 0)
             (Cexp_pair encoded_root (Cexp_num 0))))
       ==>
       candle_cv_fsn_variable_raw_jobs_check
         source_program encoded_jobs = Cexp_num 1 /\
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         tree_dim tokens encoded_jobs (Cexp_num 0) =
       Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 0)
           (Cexp_pair encoded_root (Cexp_num 0)))`,
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check_def;
       injectivity "cval"]);;

let candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_accept =
  prove
   (`!source_e (type_witness:real^N) tokens encoded_jobs encoded_root.
       candle_analytic_valid_dim (dimindex (:N)) source_e /\
       candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_check
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
              candle_cv_q_dim_taylor_model_fixed_nonlinear_variable_complete_components)
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
                candle_cv_fsn_variable_raw_jobs_check_representation_accept)
              numerical));
      ALL_TAC] THEN
    SUBGOAL_THEN
     `candle_q_dim_taylor_model_fixed_nonlinear_variable_jobs_accept
        source_e (candle_cv_fso_variable_jobs_decode encoded_jobs)`
      (LABEL_TAC "accepted") THENL
     [USE_THEN "numerical"
        (fun numerical ->
          ACCEPT_TAC
            (MATCH_MP
              (SPECL
                [`encoded_jobs:cval`;`source_e:candle_analytic_expr`]
                candle_cv_fsn_variable_raw_jobs_check_accept)
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
                      candle_q_dim_taylor_model_fixed_nonlinear_variable_compact_sound)
                    (CONJ valid (CONJ accepted logical_run)))))));;

end;;
