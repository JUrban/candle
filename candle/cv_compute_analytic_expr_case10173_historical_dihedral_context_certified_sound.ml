(* ========================================================================== *)
(* Case-10173 historical splice: checked contextual leaf acceptance.          *)
(*                                                                            *)
(* This is the numerical-to-source seam for one certificate leaf.  A checked *)
(* executable verdict is identified with the logical contextual result; the  *)
(* reusable Taylor invariant then proves strict negativity of the unchanged  *)
(* source expression throughout the leaf box.                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_context_invariant.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_certified_sound.ml";;

module Candle_cv_analytic_expr_case10173_historical_dihedral_context_certified_sound = struct

open M_verifier;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_analytic_sound;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_context_invariant;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_certified_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound;;
open Candle_cv_whole_box_dim_taylor;;

let candle_case10173_hist_checked_context_certified_accept_sound = prove
 (`!context center_factor box_factor center_program box_program boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud reported_upper.
     candle_case10173_hist_context_valid 6 context /\
     candle_analytic_valid_dim 6 box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context center_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix context box_factor) /\
     candle_cv_case10173_hist_certified_check
       center_program box_program (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
       Cexp_pair (Cexp_num 1) reported_upper
     ==>
     !(p:real^6). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim
         (candle_case10173_hist_context_box_expr context
           (candle_case10173_hist_source_dihedral_expr
             box_lp box_ln box_ld box_up box_un box_ud)
           box_factor) p < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`context:(candle_analytic_expr#candle_analytic_expr)list`;
       `center_factor:candle_analytic_expr`;
       `box_factor:candle_analytic_expr`;
       `center_program:cval`; `box_program:cval`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`;
       `center_lp:num`; `center_ln:num`; `center_ld:num`;
       `center_up:num`; `center_un:num`; `center_ud:num`;
       `box_lp:num`; `box_ln:num`; `box_ld:num`;
       `box_up:num`; `box_un:num`; `box_ud:num`]
      candle_case10173_hist_checked_context_program_invariant) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN
      (X_CHOOSE_THEN `result:candle_fsa_logical_item_type`
        STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (vec 0:real^6) boxes (candle_fsa_logical_item_q_view result)
      (candle_case10173_hist_context_center_expr context
        (candle_case10173_hist_source_dihedral_expr
          center_lp center_ln center_ld center_up center_un center_ud)
        center_factor)
      (candle_case10173_hist_context_box_expr
        (context:(candle_analytic_expr#candle_analytic_expr)list)
        (candle_case10173_hist_source_dihedral_expr
          box_lp box_ln box_ld box_up box_un box_ud)
        box_factor)`
   (LABEL_TAC "q_invariant") THENL
   [MATCH_MP_TAC candle_fsa_logical_item_q_view_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_domain
      (candle_fsa_logical_item_q_view result) /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_taylor_model_certified_upper
         (candle_fsa_logical_item_q_view result)))`
   STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ASSUME
        `candle_cv_case10173_hist_certified_check
           center_program box_program (candle_cv_q_interval_list boxes)
           (candle_cv_fs_interval_list
             [center_root_delta;center_root_four_x0;
              box_root_delta;box_root_four_x0]) =
         Cexp_pair (Cexp_num 1) reported_upper`) THEN
    REWRITE_TAC[candle_cv_case10173_hist_certified_check_def] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_cv_q_dim_taylor_model_certified_finish_correct] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[injectivity "cval"] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
    (ISPECL
      [`candle_case10173_hist_context_center_expr
          (context:(candle_analytic_expr#candle_analytic_expr)list)
          (candle_case10173_hist_source_dihedral_expr
            center_lp center_ln center_ld center_up center_un center_ud)
          center_factor`;
       `candle_case10173_hist_context_box_expr
          (context:(candle_analytic_expr#candle_analytic_expr)list)
          (candle_case10173_hist_source_dihedral_expr
            box_lp box_ln box_ld box_up box_un box_ud)
          box_factor`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `candle_fsa_logical_item_q_view
          (result:candle_fsa_logical_item_type)`;
       `(vec 0:real^6)`]
      candle_q_dim_taylor_model_invariant_accept_sound) THEN
  ASM_REWRITE_TAC[]);;

(* The batch checker observes only the Boolean first component of the
   certified result.  This form proves that such an accepted flag has the
   exact pair shape required above; no unchecked truthy cval may authorize a
   leaf. *)

let candle_case10173_hist_checked_context_certified_flag_sound = prove
 (`!context center_factor box_factor center_program box_program boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     candle_case10173_hist_context_valid 6 context /\
     candle_analytic_valid_dim 6 box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context center_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix context box_factor) /\
     Cexp_if
       (Cexp_fst
         (candle_cv_case10173_hist_certified_check
           center_program box_program (candle_cv_q_interval_list boxes)
           (candle_cv_fs_interval_list
             [center_root_delta;center_root_four_x0;
              box_root_delta;box_root_four_x0])))
       (Cexp_num 1) (Cexp_num 0) = Cexp_num 1
     ==>
     !(p:real^6). p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
       ==>
       candle_analytic_denote_dim
         (candle_case10173_hist_context_box_expr context
           (candle_case10173_hist_source_dihedral_expr
             box_lp box_ln box_ld box_up box_un box_ud)
           box_factor) p < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`context:(candle_analytic_expr#candle_analytic_expr)list`;
       `center_factor:candle_analytic_expr`;
       `box_factor:candle_analytic_expr`;
       `center_program:cval`; `box_program:cval`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `center_root_delta:(num#num)#(num#num)`;
       `center_root_four_x0:(num#num)#(num#num)`;
       `box_root_delta:(num#num)#(num#num)`;
       `box_root_four_x0:(num#num)#(num#num)`;
       `center_lp:num`; `center_ln:num`; `center_ld:num`;
       `center_up:num`; `center_un:num`; `center_ud:num`;
       `box_lp:num`; `box_ln:num`; `box_ld:num`;
       `box_up:num`; `box_un:num`; `box_ud:num`]
      candle_case10173_hist_checked_context_program_invariant) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN
      (X_CHOOSE_THEN `result:candle_fsa_logical_item_type`
        STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_analytic_invariant
      (vec 0:real^6) boxes (candle_fsa_logical_item_q_view result)
      (candle_case10173_hist_context_center_expr context
        (candle_case10173_hist_source_dihedral_expr
          center_lp center_ln center_ld center_up center_un center_ud)
        center_factor)
      (candle_case10173_hist_context_box_expr
        (context:(candle_analytic_expr#candle_analytic_expr)list)
        (candle_case10173_hist_source_dihedral_expr
          box_lp box_ln box_ld box_up box_un box_ud)
        box_factor)`
   (LABEL_TAC "q_invariant") THENL
   [MATCH_MP_TAC candle_fsa_logical_item_q_view_analytic_invariant THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_q_dim_taylor_model_result_domain
      (candle_fsa_logical_item_q_view result) /\
    ~(candle_q_le candle_q_zero
       (candle_q_dim_taylor_model_certified_upper
         (candle_fsa_logical_item_q_view result)))`
   STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ASSUME
        `Cexp_if
          (Cexp_fst
            (candle_cv_case10173_hist_certified_check
              center_program box_program (candle_cv_q_interval_list boxes)
              (candle_cv_fs_interval_list
                [center_root_delta;center_root_four_x0;
                 box_root_delta;box_root_four_x0])))
          (Cexp_num 1) (Cexp_num 0) = Cexp_num 1`) THEN
    REWRITE_TAC[candle_cv_case10173_hist_certified_check_def] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[candle_cv_q_dim_taylor_model_certified_finish_correct;
                cexp_fst_def] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def;injectivity "cval"] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC
    (ISPECL
      [`candle_case10173_hist_context_center_expr
          (context:(candle_analytic_expr#candle_analytic_expr)list)
          (candle_case10173_hist_source_dihedral_expr
            center_lp center_ln center_ld center_up center_un center_ud)
          center_factor`;
       `candle_case10173_hist_context_box_expr
          (context:(candle_analytic_expr#candle_analytic_expr)list)
          (candle_case10173_hist_source_dihedral_expr
            box_lp box_ln box_ld box_up box_un box_ud)
          box_factor`;
       `boxes:(((num#num)#num)#((num#num)#num))list`;
       `candle_fsa_logical_item_q_view
          (result:candle_fsa_logical_item_type)`;
       `(vec 0:real^6)`]
      candle_q_dim_taylor_model_invariant_accept_sound) THEN
  ASM_REWRITE_TAC[]);;

(* Transport the contextual leaf theorem back to the authenticated source
   expression.  Certificate endpoints are deliberately erased at this seam:
   their only authority comes from the checked numerical verdict above. *)

let candle_case10173_hist_checked_context_source_cell_sound = prove
 (`!source_e context center_factor box_factor center_program box_program boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud reported_upper.
     candle_case10173_hist_context_valid 6 context /\
     candle_analytic_valid_dim 6 box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context center_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix context box_factor) /\
     candle_analytic_erase_sqrt_certificates source_e =
       candle_analytic_erase_sqrt_certificates
         (candle_case10173_hist_context_box_expr context
           (candle_case10173_hist_source_dihedral_expr
             box_lp box_ln box_ld box_up box_un box_ud)
           box_factor) /\
     candle_cv_case10173_hist_certified_check
       center_program box_program (candle_cv_q_interval_list boxes)
       (candle_cv_fs_interval_list
         [center_root_delta;center_root_four_x0;
          box_root_delta;box_root_four_x0]) =
       Cexp_pair (Cexp_num 1) reported_upper
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector boxes:real^6),
        candle_q_box_upper_vector boxes)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[m_cell_pass] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(candle_analytic_denote_dim source_e:real^6->real) =
    candle_analytic_denote_dim
      (candle_case10173_hist_context_box_expr
        (context:(candle_analytic_expr#candle_analytic_expr)list)
        (candle_case10173_hist_source_dihedral_expr
          box_lp box_ln box_ld box_up box_un box_ud)
        box_factor)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_analytic_denote_certificate_transport THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (ISPECL
        [`context:(candle_analytic_expr#candle_analytic_expr)list`;
         `center_factor:candle_analytic_expr`;
         `box_factor:candle_analytic_expr`;
         `center_program:cval`; `box_program:cval`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_root_delta:(num#num)#(num#num)`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `box_root_delta:(num#num)#(num#num)`;
         `box_root_four_x0:(num#num)#(num#num)`;
         `center_lp:num`; `center_ln:num`; `center_ld:num`;
         `center_up:num`; `center_un:num`; `center_ud:num`;
         `box_lp:num`; `box_ln:num`; `box_ld:num`;
         `box_up:num`; `box_un:num`; `box_ud:num`;
         `reported_upper:cval`]
        candle_case10173_hist_checked_context_certified_accept_sound) THEN
    ASM_REWRITE_TAC[]]);;

let candle_case10173_hist_checked_context_source_cell_flag_sound = prove
 (`!source_e context center_factor box_factor center_program box_program boxes
      center_root_delta center_root_four_x0
      box_root_delta box_root_four_x0
      center_lp center_ln center_ld center_up center_un center_ud
      box_lp box_ln box_ld box_up box_un box_ud.
     candle_case10173_hist_context_valid 6 context /\
     candle_analytic_valid_dim 6 box_factor /\
     candle_analytic_erase_sqrt_certificates center_factor =
       candle_analytic_erase_sqrt_certificates box_factor /\
     LENGTH boxes = 6 /\
     candle_q_box_valid_list boxes /\
     candle_case10173_hist_root_record_valid boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_case10173_hist_production_guard boxes
       [center_root_delta;center_root_four_x0;
        box_root_delta;box_root_four_x0] /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) center_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_center_prefix context)
         (candle_case10173_hist_context_center_suffix
           context center_factor) /\
     candle_cv_case10173_hist_splice_aux (Cexp_num 31) box_program =
       candle_cv_case10173_hist_program_of
         (candle_case10173_hist_context_box_prefix context)
         (candle_case10173_hist_context_box_suffix context box_factor) /\
     candle_analytic_erase_sqrt_certificates source_e =
       candle_analytic_erase_sqrt_certificates
         (candle_case10173_hist_context_box_expr context
           (candle_case10173_hist_source_dihedral_expr
             box_lp box_ln box_ld box_up box_un box_ud)
           box_factor) /\
     Cexp_if
       (Cexp_fst
         (candle_cv_case10173_hist_certified_check
           center_program box_program (candle_cv_q_interval_list boxes)
           (candle_cv_fs_interval_list
             [center_root_delta;center_root_four_x0;
              box_root_delta;box_root_four_x0])))
       (Cexp_num 1) (Cexp_num 0) = Cexp_num 1
     ==>
     m_cell_pass
       (candle_analytic_denote_dim source_e)
       ((candle_q_box_lower_vector boxes:real^6),
        candle_q_box_upper_vector boxes)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[m_cell_pass] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(candle_analytic_denote_dim source_e:real^6->real) =
    candle_analytic_denote_dim
      (candle_case10173_hist_context_box_expr
        (context:(candle_analytic_expr#candle_analytic_expr)list)
        (candle_case10173_hist_source_dihedral_expr
          box_lp box_ln box_ld box_up box_un box_ud)
        box_factor)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC candle_analytic_denote_certificate_transport THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (ISPECL
        [`context:(candle_analytic_expr#candle_analytic_expr)list`;
         `center_factor:candle_analytic_expr`;
         `box_factor:candle_analytic_expr`;
         `center_program:cval`; `box_program:cval`;
         `boxes:(((num#num)#num)#((num#num)#num))list`;
         `center_root_delta:(num#num)#(num#num)`;
         `center_root_four_x0:(num#num)#(num#num)`;
         `box_root_delta:(num#num)#(num#num)`;
         `box_root_four_x0:(num#num)#(num#num)`;
         `center_lp:num`; `center_ln:num`; `center_ld:num`;
         `center_up:num`; `center_un:num`; `center_ud:num`;
         `box_lp:num`; `box_ln:num`; `box_ld:num`;
         `box_up:num`; `box_un:num`; `box_ud:num`]
        candle_case10173_hist_checked_context_certified_flag_sound) THEN
    ASM_REWRITE_TAC[]]);;

end;;
