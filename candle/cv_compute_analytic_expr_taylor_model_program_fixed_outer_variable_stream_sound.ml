(* ========================================================================== *)
(* Sound postorder command semantics for streamed variable certificates.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A leaf command pushes one accepted numerical  *)
(* job.  A glue command replaces the two top subtrees by their parent.  This  *)
(* logical layer is independent of the eventual raw-data transition checker; *)
(* it fixes the compact contract that such a checker must establish.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_stream_sound = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_tree_sound;;

let candle_q_dim_taylor_model_fixed_outer_variable_command_INDUCT,
    candle_q_dim_taylor_model_fixed_outer_variable_command_RECURSION =
  define_type
    "candle_q_dim_taylor_model_fixed_outer_variable_command =
       Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
         (((num#num)#num)#((num#num)#num))list
         (((num#num)#num)#((num#num)#num))list
         (((num#num)#num)#((num#num)#num))list
     | Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
         num
         (((num#num)#num)#((num#num)#num))list";;

let candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs [] =
     ([]:((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list#
           (((num#num)#num)#((num#num)#num))list))list)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          box_intervals center_intervals boxes)
        commands) =
     CONS (box_intervals,(center_intervals,boxes))
       (candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
         commands)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes)
        commands) =
     candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs commands)`;;

(* The stack is top first.  Failure is terminal: a glue with fewer than two
   predecessors returns F immediately, so later leaves cannot repair it. *)
let candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_commands_run [] stack =
     (T,stack)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_leaf
          box_intervals center_intervals boxes)
        commands) stack =
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run commands
       (CONS
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
           box_intervals center_intervals boxes)
         stack)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes)
        commands) [] =
     (F,[])) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes)
        commands) (CONS only []) =
     (F,CONS only [])) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_commands_run
      (CONS
        (Candle_q_dim_taylor_model_fixed_outer_variable_command_glue
          axis boxes)
        commands) (CONS right (CONS left stack)) =
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run commands
       (CONS
         (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
           axis boxes left right)
         stack))`;;

(* Stack jobs are read bottom-to-top.  This is invariant under replacing the
   top right/left pair by the corresponding left/right parent. *)
let candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def = define
 `(candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs [] =
     ([]:((((num#num)#num)#((num#num)#num))list#
          ((((num#num)#num)#((num#num)#num))list#
           (((num#num)#num)#((num#num)#num))list))list)) /\
  (candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs
      (CONS tree stack) =
     APPEND
       (candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs stack)
       (candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs tree))`;;

let candle_q_dim_taylor_model_fixed_outer_variable_commands_run_jobs = prove
 (`!commands stack final_stack.
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       commands stack = (T,final_stack)
     ==>
     candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs final_stack =
     APPEND
       (candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs stack)
       (candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
         commands)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def;
       candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs_def;
       APPEND;APPEND_NIL;PAIR_EQ] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_THEN (LABEL_TAC "commands_ih") THEN
    REPEAT GEN_TAC THEN
    STRUCT_CASES_TAC
      (SPEC
        `a0:candle_q_dim_taylor_model_fixed_outer_variable_command`
        (cases "candle_q_dim_taylor_model_fixed_outer_variable_command")) THENL
     [REWRITE_TAC
        [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def;
         candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs_def;
         candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
         candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def] THEN
      DISCH_THEN (LABEL_TAC "run_eq") THEN
      USE_THEN "commands_ih"
        (fun commands_ih ->
          USE_THEN "run_eq"
            (fun run_eq ->
              LABEL_TAC "run_jobs"
                (MATCH_MP
                  (SPECL
                    [`CONS
                       (Candle_q_dim_taylor_model_fixed_outer_variable_tree_leaf
                         a0' a1' a2) stack`;
                     `final_stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
                    commands_ih)
                  run_eq))) THEN
      USE_THEN "run_jobs"
        (fun run_jobs -> REWRITE_TAC [run_jobs]) THEN
      REWRITE_TAC
        [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
         candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def;
         APPEND] THEN
      ONCE_REWRITE_TAC [GSYM APPEND_ASSOC] THEN
      REWRITE_TAC [APPEND];
      STRUCT_CASES_TAC
        (ISPEC
          `stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`
          list_CASES) THENL
       [REWRITE_TAC
          [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def;
           PAIR_EQ;distinctness "bool"];
        STRUCT_CASES_TAC
          (ISPEC
            `t:candle_q_dim_taylor_model_fixed_outer_variable_tree list`
            list_CASES) THENL
         [REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def;
             PAIR_EQ;distinctness "bool"];
          REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_commands_run_def;
             candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs_def;
             candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
             candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def] THEN
          DISCH_THEN (LABEL_TAC "run_eq") THEN
          USE_THEN "commands_ih"
            (fun commands_ih ->
              USE_THEN "run_eq"
                (fun run_eq ->
                  LABEL_TAC "run_jobs"
                    (MATCH_MP
                      (SPECL
                        [`CONS
                           (Candle_q_dim_taylor_model_fixed_outer_variable_tree_node
                             a0' a1' h' h) t'`;
                         `final_stack:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
                        commands_ih)
                      run_eq))) THEN
          USE_THEN "run_jobs"
            (fun run_jobs -> REWRITE_TAC [run_jobs]) THEN
          REWRITE_TAC
            [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;
             candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs_def] THEN
          REWRITE_TAC [APPEND_ASSOC]]]]]);;

let candle_q_dim_taylor_model_fixed_outer_variable_commands_sound = prove
 (`!source_e (type_witness:real^N) commands tree.
     candle_analytic_valid_dim (dimindex (:N)) source_e /\
     candle_q_dim_taylor_model_fixed_outer_variable_jobs_accept
       source_e
       (candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs
         commands) /\
     candle_q_dim_taylor_model_fixed_outer_variable_commands_run
       commands [] = (T,[tree]) /\
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
   `candle_q_dim_taylor_model_fixed_outer_variable_tree_jobs tree =
    candle_q_dim_taylor_model_fixed_outer_variable_commands_jobs commands`
  SUBST1_TAC THENL
   [MP_TAC
      (SPECL
        [`commands:candle_q_dim_taylor_model_fixed_outer_variable_command list`;
         `[]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`;
         `[tree]:candle_q_dim_taylor_model_fixed_outer_variable_tree list`]
        candle_q_dim_taylor_model_fixed_outer_variable_commands_run_jobs) THEN
    ASM_REWRITE_TAC
      [candle_q_dim_taylor_model_fixed_outer_variable_stack_jobs_def;APPEND];
    ASM_REWRITE_TAC[]]);;

print_endline
  "CANDLE_CV_FIXED_OUTER_VARIABLE_STREAM_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
