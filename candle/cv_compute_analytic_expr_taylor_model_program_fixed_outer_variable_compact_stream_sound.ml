(* ========================================================================== *)
(* Representation soundness for the reflected compact topology stream.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_tree_compact;;
open Candle_cv_analytic_expr_taylor_model_tree_compact_correct;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stack_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_compact_stream_compute;;
open Candle_cv_whole_box_dim_taylor;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def =
  define
   `(candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token
       Candle_q_dim_taylor_model_fixed_outer_variable_compact_leaf =
      Cexp_num 0) /\
    (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token
       (Candle_q_dim_taylor_model_fixed_outer_variable_compact_glue axis) =
      Cexp_pair (Cexp_num axis) (Cexp_num 0))`;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def =
  define
   `(candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens [] =
      Cexp_num 0) /\
    (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
       (CONS token tokens) =
      Cexp_pair
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token token)
        (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
          tokens))`;;

let candle_cv_q_boxes_stack_def = define
 `(candle_cv_q_boxes_stack [] = Cexp_num 0) /\
  (candle_cv_q_boxes_stack (CONS boxes stack) =
     Cexp_pair (candle_cv_q_interval_list boxes)
       (candle_cv_q_boxes_stack stack))`;;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def =
  new_definition
   `candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result result =
      Cexp_pair (candle_cv_bool (FST result))
        (Cexp_pair
          (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs
            (FST (SND result)))
          (candle_cv_q_boxes_stack (SND (SND result))))`;;

let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE join begin";;
let candle_cv_q_boxes_compact_join_correct = prove
 (`!left right.
     candle_cv_q_boxes_compact_join
       (candle_cv_q_interval_list left)
       (candle_cv_q_interval_list right) =
     candle_cv_q_interval_list
       (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
         left right)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THEN
    REWRITE_TAC
      [candle_cv_q_interval_list_def;
       candle_cv_q_boxes_compact_join_def;
       candle_q_dim_taylor_model_fixed_outer_variable_compact_join_def];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:(((num#num)#num)#((num#num)#num))list`
        list_CASES) THEN
    ASM_REWRITE_TAC
      [candle_cv_q_interval_list_def;candle_cv_q_interval_def;
       candle_cv_q_boxes_compact_join_def;
       candle_q_dim_taylor_model_fixed_outer_variable_compact_join_def;
       cexp_fst_def;cexp_snd_def;FST;SND]]);;
let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE join end";;

let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE injective begin";;
let candle_cv_q_interval_list_injective = prove
 (`!left right.
     candle_cv_q_interval_list left = candle_cv_q_interval_list right <=>
     left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_q_interval_list_decode`) THEN
    REWRITE_TAC[candle_cv_q_interval_list_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_injective = prove
 (`!left right.
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs left =
     candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs right <=>
     left = right`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_fso_variable_jobs_decode`) THEN
    REWRITE_TAC[candle_cv_fso_variable_jobs_decode_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_q_boxes_stack_injective = prove
 (`!left right. candle_cv_q_boxes_stack left = candle_cv_q_boxes_stack right <=>
     left = right`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    REWRITE_TAC
      [candle_cv_q_boxes_stack_def;distinctness "cval";
       injectivity "cval";distinctness "list"];
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    STRUCT_CASES_TAC
      (ISPEC
        `right:((((num#num)#num)#((num#num)#num))list)list`
        list_CASES) THEN
    ASM_REWRITE_TAC
      [candle_cv_q_boxes_stack_def;distinctness "cval";
       injectivity "cval";distinctness "list";injectivity "list";
       candle_cv_q_interval_list_injective]]);;

let candle_cv_bool_injective = prove
 (`!left right. candle_cv_bool left = candle_cv_bool right <=> left = right`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `left:bool` THEN
  BOOL_CASES_TAC `right:bool` THEN
  REWRITE_TAC[candle_cv_bool_def;injectivity "cval"] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_injective =
  prove
   (`!left_success left_jobs left_stack
       right_success right_jobs right_stack.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result
         (left_success,(left_jobs,left_stack)) =
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result
         (right_success,(right_jobs,right_stack)) <=>
       left_success = right_success /\
       left_jobs = right_jobs /\ left_stack = right_stack`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
       candle_cv_bool_injective;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_injective;
       candle_cv_q_boxes_stack_injective;injectivity "cval";FST;SND] THEN
    MESON_TAC[]);;

let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_injective_all =
  prove
   (`!left right.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result left =
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result right
       <=> left = right`,
    REWRITE_TAC
      [FORALL_PAIR_THM;
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_injective;
       PAIR_EQ]);;
let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE injective end";;

let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE run begin";;
let candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_correct =
  prove
   (`!tokens tree_dim jobs stack.
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run
         (Cexp_num tree_dim)
         (candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens
           tokens)
         (candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs jobs)
         (candle_cv_q_boxes_stack stack) =
       candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result
         (candle_q_dim_taylor_model_fixed_outer_variable_compact_run
           tree_dim tokens jobs stack)`,
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC
        [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
         candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
         candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
         candle_cv_bool_def;cexp_eq_def;cexp_if_def;FST;SND;ONE];
      REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "tokens_ih") THEN
      REPEAT GEN_TAC THEN
      STRUCT_CASES_TAC
        (SPEC
          `a0:candle_q_dim_taylor_model_fixed_outer_variable_compact_token`
          (cases
            "candle_q_dim_taylor_model_fixed_outer_variable_compact_token")) THENL
       [STRUCT_CASES_TAC
          (ISPEC
            `jobs:((((num#num)#num)#((num#num)#num))list#
                   ((((num#num)#num)#((num#num)#num))list#
                    (((num#num)#num)#((num#num)#num))list))list`
            list_CASES) THENL
         [REWRITE_TAC
            [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
             candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_boxes_stack_def;candle_cv_bool_def;
             candle_cv_bool_and_def;cexp_eq_def;cexp_if_def;
             cexp_ispair_def;cexp_fst_def;cexp_snd_def;
             LET_DEF;LET_END_DEF;FST;SND];
          REWRITE_TAC
            [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
             candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_boxes_stack_def;
             candle_cv_bool_and_correct;candle_cv_bool_if_correct;
             candle_cv_interval_list_length_correct;
             candle_cv_num_equal_correct;
             cexp_ispair_def;cexp_fst_def;cexp_snd_def;
             LET_DEF;LET_END_DEF;FST;SND] THEN
          ASM_CASES_TAC `LENGTH (SND (SND h)) = tree_dim` THEN
          ASM_REWRITE_TAC
            [candle_cv_bool_and_correct;candle_cv_bool_if_correct] THEN
          ASM_REWRITE_TAC
            [candle_cv_bool_def;candle_cv_bool_and_def;cexp_if_def;
             cexp_fst_def;cexp_snd_def;FST;SND;ONE] THEN
          ASM_REWRITE_TAC
            [candle_cv_bool_def;candle_cv_bool_and_def;cexp_if_def;
             cexp_fst_def;cexp_snd_def;FST;SND;ONE] THEN
          ASM_REWRITE_TAC[] THEN
          REWRITE_TAC
            [GSYM (CONJUNCT2 candle_cv_q_boxes_stack_def)] THEN
          USE_THEN "tokens_ih" (fun theorem -> ASM_REWRITE_TAC[theorem]) THEN
          COND_CASES_TAC THEN
          ASM_REWRITE_TAC
            [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
             candle_cv_bool_def;cexp_if_def;FST;SND;ONE]];
        STRUCT_CASES_TAC
          (ISPEC
            `stack:((((num#num)#num)#((num#num)#num))list)list`
            list_CASES) THENL
         [REWRITE_TAC
            [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
             candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
             candle_cv_q_boxes_stack_def;candle_cv_bool_def;
             candle_cv_bool_and_def;cexp_eq_def;cexp_if_def;
             cexp_ispair_def;cexp_fst_def;cexp_snd_def;
             LET_DEF;LET_END_DEF;FST;SND];
          STRUCT_CASES_TAC
            (ISPEC
              `t:((((num#num)#num)#((num#num)#num))list)list`
              list_CASES) THENL
           [REWRITE_TAC
              [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
               candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
               candle_cv_q_boxes_stack_def;candle_cv_bool_def;
               candle_cv_bool_and_def;cexp_eq_def;cexp_if_def;
               cexp_ispair_def;cexp_fst_def;cexp_snd_def;
               LET_DEF;LET_END_DEF;FST;SND];
            REWRITE_TAC
              [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_tokens_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_token_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_transition_def;
               candle_q_dim_taylor_model_fixed_outer_variable_compact_run_def;
               candle_cv_q_boxes_stack_def;
               candle_cv_bool_and_correct;candle_cv_bool_if_correct;
               candle_cv_interval_list_length_correct;
               candle_cv_num_equal_correct;candle_cv_num_less_correct;
               candle_cv_q_boxes_compact_join_correct;
               candle_cv_q_boxes_split_exact_from_correct;
               cexp_add_def;cexp_ispair_def;cexp_fst_def;cexp_snd_def;
               LET_DEF;LET_END_DEF;FST;SND] THEN
            ASM_CASES_TAC
              `LENGTH
                 (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
                   h' h) = tree_dim` THEN
            ASM_CASES_TAC `1 <= a` THEN
            ASM_CASES_TAC `a <= tree_dim` THEN
            ASM_CASES_TAC
              `candle_q_boxes_split_exact_from 1 a
                 (candle_q_dim_taylor_model_fixed_outer_variable_compact_join
                   h' h)
                 h' h` THEN
            ASM_REWRITE_TAC
              [candle_cv_bool_and_correct;candle_cv_bool_if_correct;
               ARITH_RULE `a < tree_dim + 1 <=> a <= tree_dim`;
               ARITH_RULE `0 < a <=> 1 <= a`] THEN
            ASM_REWRITE_TAC
              [candle_cv_bool_def;candle_cv_bool_and_def;cexp_if_def;
               cexp_fst_def;cexp_snd_def;FST;SND;ONE] THEN
            ASM_REWRITE_TAC
              [candle_cv_bool_def;candle_cv_bool_and_def;cexp_if_def;
               cexp_fst_def;cexp_snd_def;FST;SND;ONE] THEN
            ASM_REWRITE_TAC[] THEN
            REWRITE_TAC
              [GSYM (CONJUNCT2 candle_cv_q_boxes_stack_def)] THEN
            USE_THEN "tokens_ih" (fun theorem -> ASM_REWRITE_TAC[theorem]) THEN
            COND_CASES_TAC THEN
            ASM_REWRITE_TAC
              [candle_cv_q_dim_taylor_model_fixed_outer_variable_compact_result_def;
               candle_cv_q_dim_taylor_model_fixed_outer_variable_jobs_def;
               candle_cv_bool_def;cexp_if_def;FST;SND;ONE]]]]]);;
let _ = print_endline "CANDLE_CV_COMPACT_STREAM_SOUND_PHASE run end";;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_COMPACT_STREAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
