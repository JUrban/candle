(* ========================================================================== *)
(* Sound compact postorder stream over an independently authenticated job list. *)
(*                                                                            *)
(* A leaf token consumes the next numerical job; it does not repeat that job  *)
(* in the topology stream.  A glue token combines the two top subtrees.  The  *)
(* conservation theorem proves that success cannot omit, duplicate, or reorder *)
(* jobs, and the final theorem returns one source-level root result.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_token_stream_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_token_INDUCT,
    candle_q_dim_taylor_model_fixed_outer_variable_token_RECURSION =
  define_type
    "candle_q_dim_taylor_model_fixed_outer_variable_token =
       Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf
     | Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
         num
         (((num#num)#num)#((num#num)#num))list";;

(* The result is (success,(unconsumed jobs,top-first tree stack)).  Failure is
   terminal, so a malformed prefix cannot be repaired by later tokens. *)
let candle_q_dim_taylor_model_fixed_outer_variable_token_run_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_token_run
      [] jobs stack = (T,(jobs,stack))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_token_run
      (CONS
        Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf tokens)
      [] stack = (F,([],stack))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_token_run
      (CONS
        Candle_q_dim_taylor_model_fixed_outer_variable_token_leaf tokens)
      (CONS job jobs) stack =
     candle_q_dim_taylor_model_fixed_outer_variable_token_run tokens jobs
       (CONS
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
           (FST job) (FST (SND job)) (SND (SND job)))
         stack)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_token_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
          axis boxes)
        tokens)
      jobs [] = (F,(jobs,[]))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_token_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
          axis boxes)
        tokens)
      jobs (CONS only []) = (F,(jobs,CONS only []))) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_token_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_token_glue
          axis boxes)
        tokens)
      jobs (CONS right (CONS left stack)) =
     candle_q_dim_taylor_model_fixed_outer_variable_token_run tokens jobs
       (CONS
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
           axis boxes left right)
         stack))`;;

(* Successful execution conserves the bottom-to-top leaf-job sequence. *)
let candle_q_dim_taylor_model_fixed_outer_variable_token_run_jobs = prove
 (`!tokens jobs stack remaining_jobs final_stack.
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       tokens jobs stack = (T,(remaining_jobs,final_stack))
     ==>
     APPEND
       (candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs final_stack)
       remaining_jobs =
     APPEND
       (candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs stack)
       jobs`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def;
       PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "tokens_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (SPEC
        `a0:candle_q_dim_taylor_model_fixed_outer_variable_token`
        (cases
          "candle_q_dim_taylor_model_fixed_outer_variable_token")) THENL
     [STRUCT_CASES_TAC
        (ISPEC
          `jobs:((((num#num)#num)#((num#num)#num))list#
                 ((((num#num)#num)#((num#num)#num))list#
                  (((num#num)#num)#((num#num)#num))list))list`
          list_CASES) THENL
       [REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def;
           PAIR_EQ;distinctness "bool"];
        REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def] THEN
        DISCH_THEN (LABEL_TAC "run_eq") THEN
        USE_THEN "tokens_ih"
          (fun tokens_ih ->
            USE_THEN "run_eq"
              (fun run_eq ->
                LABEL_TAC "run_jobs"
                  (MATCH_MP
                    (SPECL
                      [`t:((((num#num)#num)#((num#num)#num))list#
                           ((((num#num)#num)#((num#num)#num))list#
                            (((num#num)#num)#((num#num)#num))list))list`;
                       `CONS
                         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
                           (FST h) (FST (SND h)) (SND (SND h))) stack`;
                       `remaining_jobs:((((num#num)#num)#((num#num)#num))list#
                         ((((num#num)#num)#((num#num)#num))list#
                          (((num#num)#num)#((num#num)#num))list))list`;
                       `final_stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
                      tokens_ih)
                    run_eq))) THEN
        USE_THEN "run_jobs"
          (fun run_jobs -> REWRITE_TAC [run_jobs]) THEN
        REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
           candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;
           FST;SND] THEN
        ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
        REWRITE_TAC [APPEND]];
      STRUCT_CASES_TAC
        (ISPEC
          `stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`
          list_CASES) THENL
       [REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def;
           PAIR_EQ;distinctness "bool"];
        STRUCT_CASES_TAC
          (ISPEC
            `t:candle_q_dim_taylor_model_fixed_outer_variable_tree list`
            list_CASES) THENL
         [REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def;
             PAIR_EQ;distinctness "bool"];
          REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_token_run_def] THEN
          DISCH_THEN (LABEL_TAC "run_eq") THEN
          USE_THEN "tokens_ih"
            (fun tokens_ih ->
              USE_THEN "run_eq"
                (fun run_eq ->
                  LABEL_TAC "run_jobs"
                    (MATCH_MP
                      (SPECL
                        [`jobs:((((num#num)#num)#((num#num)#num))list#
                          ((((num#num)#num)#((num#num)#num))list#
                           (((num#num)#num)#((num#num)#num))list))list`;
                         `CONS
                           (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
                             a0' a1' h' h) t'`;
                         `remaining_jobs:((((num#num)#num)#((num#num)#num))list#
                           ((((num#num)#num)#((num#num)#num))list#
                            (((num#num)#num)#((num#num)#num))list))list`;
                         `final_stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
                        tokens_ih)
                      run_eq))) THEN
          USE_THEN "run_jobs"
            (fun run_jobs -> REWRITE_TAC [run_jobs]) THEN
          REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
             candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;
             APPEND_ASSOC]]]]]);;

let candle_q_dim_taylor_model_fixed_outer_variable_token_sound = prove
 (`!source_e (type_witness:real^N) tokens jobs tree.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e jobs /\
     candle_q_dim_taylor_model_fixed_outer_variable_token_run
       tokens jobs [] = (T,([],[tree])) /\
     candle_q_dim_taylor_model_fixed_outer_variable_tree_exact
       (dimindex (:N)) tree
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector
          (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
            tree):real^N),
        (candle_q_box_upper_vector
          (candle_q_dim_taylor_model_fixed_outer_variable_tree_root_boxes
            tree):real^N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
    (ISPECL
      [`source_e:candle_analytic_expr`;`type_witness:real^N`;
       `tree:candle_q_dim_taylor_model_fixed_outer_variable_tree`]
      candle_q_dim_taylor_model_fixed_outer_variable_tree_sound) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs tree = jobs`
  SUBST1_TAC THENL
   [MP_TAC
      (SPECL
        [`tokens:candle_q_dim_taylor_model_fixed_outer_variable_token list`;
         `jobs:((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list#
            (((num#num)#num)#((num#num)#num))list))list`;
         `[]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`;
         `[]:((((num#num)#num)#((num#num)#num))list#
           ((((num#num)#num)#((num#num)#num))list#
            (((num#num)#num)#((num#num)#num))list))list`;
         `[tree]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
        candle_q_dim_taylor_model_fixed_outer_variable_token_run_jobs) THEN
    ASM_REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
       APPEND;APPEND_NIL];
    ASM_REWRITE_TAC[]]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_TOKEN_STREAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
