(* ========================================================================== *)
(* Compilation invariant for the fixed-polynomial analytic Taylor program.  *)
(*                                                                            *)
(* This is the established analytic-expression structural induction with    *)
(* exactly one semantic change: polynomial leaves use the proved fixed-scale *)
(* result invariant.  Every nonlinear constructor reuses its existing       *)
(* preservation theorem and fail-closed domain guard.                        *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_compile_sound = struct

open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_program;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_compile_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;

let candle_q_dim_taylor_model_fixed_compile_run_analytic_invariant = prove
 (`!box_e center_e boxes stack (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes
     ==>
     ?result.
       candle_q_dim_taylor_model_program_fixed_run
         (candle_q_center_environment_list boxes) boxes
         (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
         (candle_analytic_compile center_e)
         (candle_analytic_compile box_e) stack = CONS result stack /\
       candle_q_dim_taylor_model_result_analytic_invariant
         type_witness boxes result center_e box_e`,
  MATCH_MP_TAC candle_analytic_expr_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:candle_poly_expr` THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN `center_e = Candle_analytic_poly p` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL [`center_e:candle_analytic_expr`; `p:candle_poly_expr`]
             candle_analytic_erase_poly_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_fs_poly_program_to_q
       (candle_q_center_environment_list boxes)
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (candle_poly_compile p)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def;
                  candle_q_dim_taylor_model_program_fixed_run_def;
                  candle_q_dim_taylor_model_program_fixed_step_poly];
      MATCH_MP_TAC
        candle_fs_poly_program_to_q_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_neg center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_neg_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_neg
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_single THEN
      EXISTS_TAC
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list` THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_neg] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_neg_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    MAP_EVERY X_GEN_TAC
      [`a:candle_analytic_expr`; `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a center_b.
        center_e = Candle_analytic_add center_a center_b /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a /\
        candle_analytic_erase_sqrt_certificates center_b =
          candle_analytic_erase_sqrt_certificates b`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (X_CHOOSE_THEN `center_b:candle_analytic_expr`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`;
              `b:candle_analytic_expr`]
             candle_analytic_erase_add_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?left.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS left stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes left center_a a`
     (X_CHOOSE_THEN
       `left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_b)
          (candle_analytic_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes right center_b b`
     (X_CHOOSE_THEN
       `right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_add
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)
       (right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_binary THEN
      MAP_EVERY EXISTS_TAC
       [`left:
           bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list`;
        `right:
           bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list`] THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_add] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_add_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    MAP_EVERY X_GEN_TAC
      [`a:candle_analytic_expr`; `b:candle_analytic_expr`] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "iha") (LABEL_TAC "ihb")) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a center_b.
        center_e = Candle_analytic_mul center_a center_b /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a /\
        candle_analytic_erase_sqrt_certificates center_b =
          candle_analytic_erase_sqrt_certificates b`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (X_CHOOSE_THEN `center_b:candle_analytic_expr`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`;
              `b:candle_analytic_expr`]
             candle_analytic_erase_mul_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?left.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS left stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes left center_a a`
     (X_CHOOSE_THEN
       `left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "iha" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?right.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_b)
          (candle_analytic_compile b) (CONS left stack) =
            CONS right (CONS left stack) /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes right center_b b`
     (X_CHOOSE_THEN
       `right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ihb" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_mul
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (left:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)
       (right:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_binary THEN
      MAP_EVERY EXISTS_TAC
       [`left:
           bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list`;
        `right:
           bool#
           ((((num#num)#num)#(num#num)#num)#
            (((num#num)#num)#(num#num)#num)list#
            ((((num#num)#num)#(num#num)#num)list)list)#
           (((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list`] THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_mul] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_mul_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_square center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_square_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_square
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_single THEN
      EXISTS_TAC
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list` THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_square] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_square_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_inv center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_inv_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_inv
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_single THEN
      EXISTS_TAC
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list` THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_inv] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_inv_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    MAP_EVERY X_GEN_TAC
      [`blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
       `a:candle_analytic_expr`] THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?clp cln cld cup cun cud center_a.
        center_e = Candle_analytic_sqrt clp cln cld cup cun cud center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `clp:num`
       (X_CHOOSE_THEN `cln:num`
        (X_CHOOSE_THEN `cld:num`
         (X_CHOOSE_THEN `cup:num`
          (X_CHOOSE_THEN `cun:num`
           (X_CHOOSE_THEN `cud:num`
            (X_CHOOSE_THEN `center_a:candle_analytic_expr`
              (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))))))) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_sqrt_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_sqrt
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (candle_analytic_sqrt_interval clp cln cld cup cun cud)
       (candle_analytic_sqrt_interval blp bln bld bup bun bud)
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_single THEN
      EXISTS_TAC
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list` THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_sqrt] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_sqrt_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def;
                      candle_analytic_erase_sqrt_certificates_def]];
    X_GEN_TAC `a:candle_analytic_expr` THEN
    DISCH_THEN (LABEL_TAC "ih") THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN
     `?center_a.
        center_e = Candle_analytic_atn center_a /\
        candle_analytic_erase_sqrt_certificates center_a =
          candle_analytic_erase_sqrt_certificates a`
     (X_CHOOSE_THEN `center_a:candle_analytic_expr`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPECL
             [`center_e:candle_analytic_expr`; `a:candle_analytic_expr`]
             candle_analytic_erase_atn_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?inner.
        candle_q_dim_taylor_model_program_fixed_run
          (candle_q_center_environment_list boxes) boxes
          (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
          (candle_analytic_compile center_a)
          (candle_analytic_compile a) stack = CONS inner stack /\
        candle_q_dim_taylor_model_result_analytic_invariant
          (type_witness:real^N) boxes inner center_a a`
     (X_CHOOSE_THEN
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list`
       STRIP_ASSUME_TAC) THENL
     [USE_THEN "ih" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_atn
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def] THEN
      MATCH_MP_TAC candle_q_dim_taylor_model_program_fixed_run_append_single THEN
      EXISTS_TAC
       `inner:
          bool#
          ((((num#num)#num)#(num#num)#num)#
           (((num#num)#num)#(num#num)#num)list#
           ((((num#num)#num)#(num#num)#num)list)list)#
          (((num#num)#num)#(num#num)#num)#
          (((num#num)#num)#(num#num)#num)list#
          ((((num#num)#num)#(num#num)#num)list)list` THEN
      ASM_REWRITE_TAC[candle_analytic_compile_length_certificate_equivalent;
                      candle_q_dim_taylor_model_program_fixed_step_atn] THEN
      ASM_MESON_TAC[candle_analytic_compile_length_certificate_equivalent];
      MATCH_MP_TAC candle_q_dim_taylor_model_result_atn_analytic_invariant THEN
      ASM_REWRITE_TAC[candle_analytic_valid_dim_def]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    RULE_ASSUM_TAC (REWRITE_RULE[candle_analytic_valid_dim_def]) THEN
    SUBGOAL_THEN `center_e = Candle_analytic_pi_half` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC
       (fst
         (EQ_IMP_RULE
           (SPEC `center_e:candle_analytic_expr`
             candle_analytic_erase_pi_half_eq))) THEN
      ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
      ALL_TAC] THEN
    EXISTS_TAC
     `candle_q_dim_taylor_model_result_pi_half
       (candle_q_fixed_list_round_upper (candle_q_radius_list boxes))
       (candle_q_center_environment_list boxes) boxes` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_compile_def;
                  candle_q_dim_taylor_model_program_fixed_run_def;
                  candle_q_dim_taylor_model_program_fixed_step_pi_half];
      MATCH_MP_TAC
        candle_q_dim_taylor_model_result_pi_half_analytic_invariant THEN
      ASM_REWRITE_TAC[]]]);;

end;;
