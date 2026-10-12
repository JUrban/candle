(* ========================================================================== *)
(* Case-10173 historical splice: compositional logical program semantics.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_item_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_program_logical_sound = struct

open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_program_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_item_sound;;

(* Ordinary theorem-level stack item denoted by private instruction 9. *)

let candle_case10173_hist_logical_item_def = new_definition
 `candle_case10173_hist_logical_item center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0 =
    let result =
      candle_case10173_hist_result center_boxes boxes radii
        center_root_delta center_root_four_x0
        box_root_delta box_root_four_x0 in
    candle_fsa_logical_item_make T result (candle_fs_result_to_q result)`;;

let candle_cv_case10173_hist_logical_item_correct = prove
 (`!center_boxes boxes radii
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_case10173_hist_item
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
     candle_cv_fsa_logical_item_encode
       (candle_case10173_hist_logical_item center_boxes boxes radii
         center_root_delta center_root_four_x0
         box_root_delta box_root_four_x0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_case10173_hist_logical_item_def;
              candle_cv_fsa_logical_item_encode_def;
              candle_fsa_logical_item_make_def;
              candle_fsa_logical_item_tag_def;
              candle_fsa_logical_item_fixed_def;
              candle_fsa_logical_item_q_def;
              candle_cv_case10173_hist_item_encode_correct;
              LET_DEF; LET_END_DEF]);;

(* A source program with an ordinary prefix and suffix around instruction 9. *)

let candle_cv_case10173_hist_program_of_def = define
 `(candle_cv_case10173_hist_program_of [] suffix =
     Cexp_pair (Cexp_num 9)
       (candle_cv_analytic_instruction_list suffix)) /\
  (candle_cv_case10173_hist_program_of (CONS h t) suffix =
     Cexp_pair (candle_cv_analytic_instruction h)
       (candle_cv_case10173_hist_program_of t suffix))`;;

let candle_cv_case10173_hist_drop_segment = prove
 (`!suffix i0 i1 i2 i3 i4 i5 i6 i7.
     candle_cv_case10173_hist_drop_eight
       (candle_cv_analytic_instruction_list
         (APPEND [i0;i1;i2;i3;i4;i5;i6;i7] suffix)) =
     candle_cv_analytic_instruction_list suffix`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[APPEND; candle_cv_analytic_instruction_list_def;
              candle_cv_case10173_hist_drop_eight_def; cexp_snd_def]);;

let candle_cv_case10173_hist_splice_prefix = prove
 (`!prefix tail suffix.
     candle_cv_case10173_hist_drop_eight
       (candle_cv_analytic_instruction_list tail) =
     candle_cv_analytic_instruction_list suffix
     ==>
     candle_cv_case10173_hist_splice_aux (Cexp_num (LENGTH prefix))
       (candle_cv_analytic_instruction_list (APPEND prefix tail)) =
     candle_cv_case10173_hist_program_of prefix suffix`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH; APPEND;
                candle_cv_case10173_hist_splice_aux_def;
                candle_cv_case10173_hist_program_of_def] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[LENGTH; APPEND;
                candle_cv_analytic_instruction_list_def;
                candle_cv_case10173_hist_splice_aux_def;
                candle_cv_case10173_hist_program_of_def;
                cexp_sub_def; ARITH_RULE `SUC n - 1 = n`] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let candle_cv_case10173_hist_splice_segment = prove
 (`!prefix suffix i0 i1 i2 i3 i4 i5 i6 i7.
     candle_cv_case10173_hist_splice_aux (Cexp_num (LENGTH prefix))
       (candle_cv_analytic_instruction_list
         (APPEND prefix
           (APPEND [i0;i1;i2;i3;i4;i5;i6;i7] suffix))) =
     candle_cv_case10173_hist_program_of prefix suffix`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC candle_cv_case10173_hist_splice_prefix THEN
  REWRITE_TAC[candle_cv_case10173_hist_drop_segment]);;

(* Away from private tag 9, the custom machine is exactly the proved generic
   fixed-nonlinear machine. *)

let candle_cv_case10173_hist_step_ordinary_correct = prove
 (`!center_instruction box_instruction center_boxes boxes radii stack
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_case10173_hist_step
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0])
       (candle_cv_analytic_instruction center_instruction)
       (candle_cv_analytic_instruction box_instruction)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsn_logical_program_step center_boxes boxes radii
         center_instruction box_instruction stack)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC
    (SPEC `center_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  STRUCT_CASES_TAC
    (SPEC `box_instruction:candle_analytic_instruction`
      (cases "candle_analytic_instruction")) THEN
  REWRITE_TAC[candle_cv_case10173_hist_step_def;
              candle_cv_analytic_instruction_def;
              cexp_eq_def; cexp_if_def; distinctness "cval";
              injectivity "cval"; NOT_SUC;
              candle_cv_fsn_logical_program_step_correct] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[cexp_if_def]);;

let candle_cv_case10173_hist_run_ordinary_correct = prove
 (`!center_program box_program center_boxes boxes radii stack
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     candle_cv_case10173_hist_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0])
       (candle_cv_analytic_instruction_list center_program)
       (candle_cv_analytic_instruction_list box_program)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsn_logical_program_run center_boxes boxes radii
         center_program box_program stack)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                candle_cv_case10173_hist_program_run_def;
                candle_fsn_logical_program_run_def];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC[candle_cv_analytic_instruction_list_def;
                    candle_cv_case10173_hist_program_run_def;
                    candle_fsn_logical_program_run_def;
                    candle_cv_case10173_hist_step_ordinary_correct]]);;

(* The central composition theorem: ordinary prefix, one historical item,
   then an arbitrary aligned ordinary suffix. *)

let candle_cv_case10173_hist_program_of_correct = prove
 (`!center_prefix box_prefix center_suffix box_suffix
      center_boxes boxes radii stack
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0.
     LENGTH center_prefix = LENGTH box_prefix
     ==>
     candle_cv_case10173_hist_program_run
       (candle_cv_q_interval_list center_boxes)
       (candle_cv_q_interval_list boxes)
       (candle_cv_q_list radii)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0])
       (candle_cv_case10173_hist_program_of center_prefix center_suffix)
       (candle_cv_case10173_hist_program_of box_prefix box_suffix)
       (candle_cv_fsa_logical_stack_encode stack) =
     candle_cv_fsa_logical_stack_encode
       (candle_fsn_logical_program_run center_boxes boxes radii
         center_suffix box_suffix
         (CONS
           (candle_case10173_hist_logical_item center_boxes boxes radii
             center_root_delta center_root_four_x0
             box_root_delta box_root_four_x0)
           (candle_fsn_logical_program_run center_boxes boxes radii
             center_prefix box_prefix stack)))`,
  LIST_INDUCT_TAC THENL
   [LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH] THENL
     [REWRITE_TAC[candle_cv_case10173_hist_program_of_def;
                  candle_cv_case10173_hist_program_run_def;
                  candle_cv_case10173_hist_step_def;
                  cexp_eq_def; cexp_if_def; injectivity "cval";
                  candle_fsn_logical_program_run_def;
                  candle_cv_fsa_logical_stack_encode_def;
                  candle_cv_case10173_hist_logical_item_correct] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[cexp_if_def] THEN
      MP_TAC
       (SPECL
         [`center_suffix:candle_analytic_instruction list`;
          `box_suffix:candle_analytic_instruction list`;
          `center_boxes:(((num#num)#num)#((num#num)#num))list`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `radii:((num#num)#num)list`;
          `CONS
            (candle_case10173_hist_logical_item center_boxes boxes radii
              center_root_delta center_root_four_x0
              box_root_delta box_root_four_x0)
            stack`;
          `center_root_delta:(num#num)#(num#num)`;
          `center_root_four_x0:(num#num)#(num#num)`;
          `box_root_delta:(num#num)#(num#num)`;
          `box_root_four_x0:(num#num)#(num#num)`]
         candle_cv_case10173_hist_run_ordinary_correct) THEN
      REWRITE_TAC[candle_cv_fsa_logical_stack_encode_def];
      ARITH_TAC];
    LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[LENGTH] THENL
     [ARITH_TAC;
      REWRITE_TAC[SUC_INJ;
                  candle_cv_case10173_hist_program_of_def;
                  candle_cv_case10173_hist_program_run_def;
                  candle_fsn_logical_program_run_def] THEN
      DISCH_TAC THEN
      REWRITE_TAC[candle_cv_case10173_hist_step_ordinary_correct] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

end;;
