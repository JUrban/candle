(* ========================================================================== *)
(* Analytic invariant for the reflected fixed-nonlinear program.              *)
(*                                                                            *)
(* This file deliberately sits above the stable executable-correspondence and *)
(* scalar/shape soundness layer.  Keeping the changing operation proofs here  *)
(* lets development restart from the sealed nonlinear support checkpoint.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_sound.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_invariant = struct

open Multivariate_taylor;;
open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_dim_jet_pi_half;;
open Candle_cv_analytic_expr_jet;;
open Candle_cv_analytic_expr_calculus;;
open Candle_cv_analytic_expr_domain;;
open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_taylor_model_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_sound;;
open Candle_cv_polynomial_expr_flyspeck_dim_sound;;
open Candle_cv_polynomial_expr_dim_jet;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_invariant;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_invariant;;

let candle_fsn_inv_hessian_contains = prove
 (`!n value gradient hessian value_real gradient_real hessian_real.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_q_interval_not_zero (candle_fs_interval_to_q value) /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fsn_inv_hessian value gradient hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j.
                  (--(inv value_real * inv value_real)) *
                    hessian_real i j +
                  (((inv value_real * inv value_real) * inv value_real) +
                   ((inv value_real * inv value_real) * inv value_real)) *
                    (gradient_real i * gradient_real j)) n) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_inv_hessian_def; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_neg
        (candle_fsn_interval_mul
          (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
          (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))))
      (--(inv value_real * inv value_real))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fsn_inv_square_neg_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_interval_add
        (candle_fsn_interval_mul
          (candle_fsn_interval_mul
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
          (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
        (candle_fsn_interval_mul
          (candle_fsn_interval_mul
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
          (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))))
      (((inv value_real * inv value_real) * inv value_real) +
       ((inv value_real * inv value_real) * inv value_real))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC candle_fsn_inv_cube_twice_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_matrix_scale
        (candle_fs_interval_neg
          (candle_fsn_interval_mul
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))))
        hessian)
      (list_of_seq
        (\i. list_of_seq
          (\j. (--(inv value_real * inv value_real)) *
               hessian_real i j) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_matrix_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_matrix_scale_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_outer gradient gradient)
      (list_of_seq
        (\i. list_of_seq
          (\j. gradient_real i * gradient_real j) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_outer_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_outer_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_matrix_scale
        (candle_fs_interval_add
          (candle_fsn_interval_mul
            (candle_fsn_interval_mul
              (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
              (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
          (candle_fsn_interval_mul
            (candle_fsn_interval_mul
              (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))
              (candle_fs_interval_of_q (candle_fsn_q_inv_interval value)))
            (candle_fs_interval_of_q (candle_fsn_q_inv_interval value))))
        (candle_fsn_interval_outer gradient gradient))
      (list_of_seq
        (\i. list_of_seq
          (\j.
             (((inv value_real * inv value_real) * inv value_real) +
              ((inv value_real * inv value_real) * inv value_real)) *
             (gradient_real i * gradient_real j)) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_matrix_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_matrix_scale_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM candle_map2_matrix_list_of_seq] THEN
  MATCH_MP_TAC (SPEC `n:num` candle_fs_interval_matrix_add_contains) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                  candle_fsn_interval_outer_shape];
    ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape];
    ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                  candle_fsn_interval_outer_shape];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_fsn_inv_jet_components = prove
 (`!n value gradient hessian value_real gradient_real hessian_real.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_q_interval_not_zero (candle_fs_interval_to_q value) /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> candle_q_dim_jet_contains_components n
           (candle_fs_first_to_q
             (candle_fsn_first_inv
               (candle_fs_first_make value gradient))
             (candle_fsn_inv_hessian value gradient hessian))
           (inv value_real)
           (\i. (--(inv value_real * inv value_real)) * gradient_real i)
           (\i j.
              (--(inv value_real * inv value_real)) * hessian_real i j +
              (((inv value_real * inv value_real) * inv value_real) +
               ((inv value_real * inv value_real) * inv value_real)) *
              (gradient_real i * gradient_real j))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_first_value
        (candle_fsn_first_inv
          (candle_fs_first_make value gradient)))
      (inv value_real) /\
    ALL2 candle_fs_interval_contains
      (candle_fs_first_gradient
        (candle_fsn_first_inv
          (candle_fs_first_make value gradient)))
      (list_of_seq
        (\i. (--(inv value_real * inv value_real)) * gradient_real i) n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ISPECL
        [`n:num`;
         `candle_fs_first_make
           (value:((num#num)#(num#num)))
           (gradient:((num#num)#(num#num))list)`;
         `value_real:real`;
         `gradient_real:num->real`]
        candle_fsn_first_inv_contains) THEN
    ASM_REWRITE_TAC[candle_fs_first_make_def;
                    candle_fs_first_value_def;
                    candle_fs_first_gradient_def; FST; SND];
    ALL_TAC] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_inv_jet_shape THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC
      (ISPECL
        [`n:num`;
         `value:((num#num)#(num#num))`;
         `gradient:((num#num)#(num#num))list`;
         `hessian:(((num#num)#(num#num))list)list`;
         `value_real:real`;
         `gradient_real:num->real`;
         `hessian_real:num->num->real`]
        candle_fsn_inv_hessian_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fsn_sqrt_value_contains = prove
  (`!certificate fixed_interval x.
     candle_fsn_sqrt_domain certificate fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_of_q certificate) (sqrt x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_sqrt_domain_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_interval_sqrt_certificate_sound THEN
  EXISTS_TAC `candle_fs_interval_to_q fixed_interval` THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_sqrt_domain_value_positive = prove
 (`!certificate fixed_interval x.
     candle_fsn_sqrt_domain certificate fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> &0 < x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC
    (REWRITE_RULE[candle_fsn_sqrt_domain_def; LET_DEF; LET_END_DEF]) THEN
  MP_TAC
   (ISPECL
     [`certificate:(((num#num)#num)#((num#num)#num))`;
      `candle_q_dim_jet_make
        (candle_fs_interval_to_q
          (fixed_interval:((num#num)#(num#num)))) [] []`;
      `x:real`]
     candle_q_dim_jet_sqrt_domain_value_positive) THEN
  REWRITE_TAC[candle_q_dim_jet_sqrt_domain_def;
              candle_q_dim_jet_make_def; candle_q_dim_jet_f_def;
              candle_fsn_sqrt_domain_def; LET_DEF; LET_END_DEF;
              FST; SND; candle_fs_interval_to_q_contains] THEN
  ASM_REWRITE_TAC[]);;

let candle_fsn_sqrt_d_contains = prove
 (`!certificate fixed_interval x.
     candle_fsn_sqrt_domain certificate fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_of_q
             (candle_q_dim_jet_sqrt_d certificate))
           (inv (sqrt x + sqrt x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_sqrt_domain_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_dim_jet_sqrt_d_sound THEN
  EXISTS_TAC `candle_fs_interval_to_q fixed_interval` THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_sqrt_dd_contains = prove
 (`!certificate fixed_interval x.
     candle_fsn_sqrt_domain certificate fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_of_q
             (candle_q_dim_jet_sqrt_dd certificate
               (candle_fs_interval_to_q fixed_interval)))
           (--inv ((sqrt x + sqrt x) * (x + x)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_sqrt_domain_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_dim_jet_sqrt_dd_sound THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_first_sqrt_contains = prove
 (`!n
     (certificate:(((num#num)#num)#((num#num)#num)))
     (first:(((num#num)#(num#num))#
       (((num#num)#(num#num))list)))
     (value:real) (gradient:num->real).
     candle_fsn_sqrt_domain certificate
       (candle_fs_first_value first) /\
     candle_fs_interval_contains (candle_fs_first_value first) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient first) (list_of_seq gradient n)
     ==> candle_fs_interval_contains
           (candle_fs_first_value
             (candle_fsn_first_sqrt certificate first))
           (sqrt value) /\
         ALL2 candle_fs_interval_contains
           (candle_fs_first_gradient
             (candle_fsn_first_sqrt certificate first))
           (list_of_seq
             (\i. inv (sqrt value + sqrt value) * gradient i) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_first_sqrt_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              FST; SND; LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_sqrt_value_contains THEN
    EXISTS_TAC
      `candle_fs_first_value
        (first:(((num#num)#(num#num))#
          (((num#num)#(num#num))list)))` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_list_scale_contains THEN
    ASM_REWRITE_TAC[GSYM candle_fs_first_value_def;
                    GSYM candle_fs_first_gradient_def] THEN
    MATCH_MP_TAC candle_fsn_sqrt_d_contains THEN
    EXISTS_TAC
      `candle_fs_first_value
        (first:(((num#num)#(num#num))#
          (((num#num)#(num#num))list)))` THEN
    ASM_REWRITE_TAC[]]);;

(* Both sqrt and atn use the same unary Hessian chain rule.  Proving its
   rounded fixed-scale realization once keeps the operation-specific proofs
   responsible only for their scalar derivative enclosures. *)

let candle_fsn_unary_hessian_contains = prove
 (`!n d dd gradient hessian d_real dd_real gradient_real hessian_real.
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_fs_interval_contains d d_real /\
     candle_fs_interval_contains dd dd_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fs_interval_matrix_add
             (candle_fsn_interval_matrix_scale dd
               (candle_fsn_interval_outer gradient gradient))
             (candle_fsn_interval_matrix_scale d hessian))
           (list_of_seq
             (\i. list_of_seq
               (\j. dd_real * (gradient_real i * gradient_real j) +
                    d_real * hessian_real i j) n) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_outer gradient gradient)
      (list_of_seq
        (\i. list_of_seq
          (\j. gradient_real i * gradient_real j) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_outer_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_outer_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_matrix_scale dd
        (candle_fsn_interval_outer gradient gradient))
      (list_of_seq
        (\i. list_of_seq
          (\j. dd_real * (gradient_real i * gradient_real j)) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_matrix_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_matrix_scale_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ALL2 (ALL2 candle_fs_interval_contains)
      (candle_fsn_interval_matrix_scale d hessian)
      (list_of_seq
        (\i. list_of_seq
          (\j. d_real * hessian_real i j) n) n)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM candle_map_matrix_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_matrix_scale_contains THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM candle_map2_matrix_list_of_seq] THEN
  MATCH_MP_TAC (SPEC `n:num` candle_fs_interval_matrix_add_contains) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                  candle_fsn_interval_outer_shape];
    ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape;
                  candle_fsn_interval_outer_shape];
    ASM_MESON_TAC[candle_fsn_interval_matrix_scale_shape];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_fsn_sqrt_hessian_contains = prove
 (`!n
     (certificate:(((num#num)#num)#((num#num)#num)))
     (value:((num#num)#(num#num)))
     (gradient:((num#num)#(num#num))list)
     (hessian:(((num#num)#(num#num))list)list)
     (value_real:real) (gradient_real:num->real)
     (hessian_real:num->num->real).
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_fsn_sqrt_domain certificate value /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fsn_sqrt_hessian certificate value gradient hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j.
                  (--inv
                    ((sqrt value_real + sqrt value_real) *
                     (value_real + value_real))) *
                    (gradient_real i * gradient_real j) +
                  inv (sqrt value_real + sqrt value_real) *
                    hessian_real i j) n) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_sqrt_hessian_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fsn_unary_hessian_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsn_sqrt_d_contains THEN
    EXISTS_TAC `value:((num#num)#(num#num))` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsn_sqrt_dd_contains THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_fsn_sqrt_jet_components = prove
 (`!n
     (certificate:(((num#num)#num)#((num#num)#num)))
     (value:((num#num)#(num#num)))
     (gradient:((num#num)#(num#num))list)
     (hessian:(((num#num)#(num#num))list)list)
     (value_real:real) (gradient_real:num->real)
     (hessian_real:num->num->real).
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_fsn_sqrt_domain certificate value /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> candle_q_dim_jet_contains_components n
           (candle_fs_first_to_q
             (candle_fsn_first_sqrt certificate
               (candle_fs_first_make
                 (value:((num#num)#(num#num))) gradient))
             (candle_fsn_sqrt_hessian certificate
               value gradient hessian))
           (sqrt value_real)
           (\i. inv (sqrt value_real + sqrt value_real) * gradient_real i)
           (\i j.
              (--inv
                ((sqrt value_real + sqrt value_real) *
                 (value_real + value_real))) *
                (gradient_real i * gradient_real j) +
              inv (sqrt value_real + sqrt value_real) *
                hessian_real i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_first_value
        (candle_fsn_first_sqrt certificate
          (candle_fs_first_make
            (value:((num#num)#(num#num))) gradient)))
      (sqrt value_real) /\
    ALL2 candle_fs_interval_contains
      (candle_fs_first_gradient
        (candle_fsn_first_sqrt certificate
          (candle_fs_first_make
            (value:((num#num)#(num#num))) gradient)))
      (list_of_seq
        (\i. inv (sqrt value_real + sqrt value_real) * gradient_real i) n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ISPECL
        [`n:num`;
         `certificate:(((num#num)#num)#((num#num)#num))`;
         `candle_fs_first_make
           (value:((num#num)#(num#num)))
           (gradient:((num#num)#(num#num))list)`;
         `value_real:real`;
         `gradient_real:num->real`]
        candle_fsn_first_sqrt_contains) THEN
    ASM_REWRITE_TAC[candle_fs_first_make_def;
                    candle_fs_first_value_def;
                    candle_fs_first_gradient_def; FST; SND];
    ALL_TAC] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_sqrt_jet_shape THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC
      (ISPECL
        [`n:num`;
         `certificate:(((num#num)#num)#((num#num)#num))`;
         `value:((num#num)#(num#num))`;
         `gradient:((num#num)#(num#num))list`;
         `hessian:(((num#num)#(num#num))list)list`;
         `value_real:real`;
         `gradient_real:num->real`;
         `hessian_real:num->num->real`]
        candle_fsn_sqrt_hessian_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fsn_atn_value_contains = prove
 (`!fixed_interval x.
     candle_fsn_atn_domain fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fs_interval_of_q
             (candle_q_interval_atn_range
               (candle_fs_interval_to_q fixed_interval)))
           (atn x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_atn_domain_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_interval_atn_range_sound THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_atn_d_contains = prove
 (`!fixed_interval x.
     candle_fsn_atn_domain fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fsn_atn_d_fixed fixed_interval)
           (inv (&1 + x * x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_atn_domain_def;
              candle_fsn_atn_d_fixed_def;
              LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_dim_jet_atn_d_sound THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_atn_dd_contains = prove
 (`!fixed_interval x.
     candle_fsn_atn_domain fixed_interval /\
     candle_fs_interval_contains fixed_interval x
     ==> candle_fs_interval_contains
           (candle_fsn_atn_dd_fixed fixed_interval)
           (--((x + x) *
                (inv (&1 + x * x) * inv (&1 + x * x))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_fsn_atn_domain_def;
              candle_fsn_atn_dd_fixed_def;
              LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
  MATCH_MP_TAC candle_q_dim_jet_atn_dd_sound THEN
  ASM_REWRITE_TAC[candle_fs_interval_to_q_contains]);;

let candle_fsn_first_atn_contains = prove
 (`!n
     (first:(((num#num)#(num#num))#
       (((num#num)#(num#num))list)))
     (value:real) (gradient:num->real).
     candle_fsn_atn_domain (candle_fs_first_value first) /\
     candle_fs_interval_contains (candle_fs_first_value first) value /\
     ALL2 candle_fs_interval_contains
       (candle_fs_first_gradient first) (list_of_seq gradient n)
     ==> candle_fs_interval_contains
           (candle_fs_first_value (candle_fsn_first_atn first))
           (atn value) /\
         ALL2 candle_fs_interval_contains
           (candle_fs_first_gradient (candle_fsn_first_atn first))
           (list_of_seq
             (\i. inv (&1 + value * value) * gradient i) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_first_atn_def;
              candle_fs_first_make_def;
              candle_fs_first_value_def;
              candle_fs_first_gradient_def;
              FST; SND; LET_DEF; LET_END_DEF] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_atn_value_contains THEN
    ASM_REWRITE_TAC[GSYM candle_fs_first_value_def];
    REWRITE_TAC[GSYM candle_map_scale_list_of_seq] THEN
    MATCH_MP_TAC candle_fsn_interval_list_scale_contains THEN
    ASM_REWRITE_TAC[GSYM candle_fs_first_value_def;
                    GSYM candle_fs_first_gradient_def] THEN
    MATCH_MP_TAC candle_fsn_atn_d_contains THEN
    ASM_REWRITE_TAC[]]);;

let candle_fsn_atn_hessian_contains = prove
 (`!n
     (value:((num#num)#(num#num)))
     (gradient:((num#num)#(num#num))list)
     (hessian:(((num#num)#(num#num))list)list)
     (value_real:real) (gradient_real:num->real)
     (hessian_real:num->num->real).
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_fsn_atn_domain value /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> ALL2 (ALL2 candle_fs_interval_contains)
           (candle_fsn_atn_hessian value gradient hessian)
           (list_of_seq
             (\i. list_of_seq
               (\j.
                  (--((value_real + value_real) *
                       (inv (&1 + value_real * value_real) *
                        inv (&1 + value_real * value_real)))) *
                    (gradient_real i * gradient_real j) +
                  inv (&1 + value_real * value_real) *
                    hessian_real i j) n) n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_atn_hessian_def; LET_DEF; LET_END_DEF] THEN
  MATCH_MP_TAC candle_fsn_unary_hessian_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsn_atn_d_contains THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_fsn_atn_dd_contains THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let candle_fsn_atn_jet_components = prove
 (`!n
     (value:((num#num)#(num#num)))
     (gradient:((num#num)#(num#num))list)
     (hessian:(((num#num)#(num#num))list)list)
     (value_real:real) (gradient_real:num->real)
     (hessian_real:num->num->real).
     LENGTH gradient = n /\
     LENGTH hessian = n /\
     ALL (\row. LENGTH row = n) hessian /\
     candle_fsn_atn_domain value /\
     candle_fs_interval_contains value value_real /\
     ALL2 candle_fs_interval_contains gradient
       (list_of_seq gradient_real n) /\
     ALL2 (ALL2 candle_fs_interval_contains) hessian
       (list_of_seq (\i. list_of_seq (hessian_real i) n) n)
     ==> candle_q_dim_jet_contains_components n
           (candle_fs_first_to_q
             (candle_fsn_first_atn
               (candle_fs_first_make
                 (value:((num#num)#(num#num))) gradient))
             (candle_fsn_atn_hessian value gradient hessian))
           (atn value_real)
           (\i. inv (&1 + value_real * value_real) * gradient_real i)
           (\i j.
              (--((value_real + value_real) *
                   (inv (&1 + value_real * value_real) *
                    inv (&1 + value_real * value_real)))) *
                (gradient_real i * gradient_real j) +
              inv (&1 + value_real * value_real) * hessian_real i j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `candle_fs_interval_contains
      (candle_fs_first_value
        (candle_fsn_first_atn
          (candle_fs_first_make
            (value:((num#num)#(num#num))) gradient)))
      (atn value_real) /\
    ALL2 candle_fs_interval_contains
      (candle_fs_first_gradient
        (candle_fsn_first_atn
          (candle_fs_first_make
            (value:((num#num)#(num#num))) gradient)))
      (list_of_seq
        (\i. inv (&1 + value_real * value_real) * gradient_real i) n)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC
      (ISPECL
        [`n:num`;
         `candle_fs_first_make
           (value:((num#num)#(num#num)))
           (gradient:((num#num)#(num#num))list)`;
         `value_real:real`;
         `gradient_real:num->real`]
        candle_fsn_first_atn_contains) THEN
    ASM_REWRITE_TAC[candle_fs_first_make_def;
                    candle_fs_first_value_def;
                    candle_fs_first_gradient_def; FST; SND];
    ALL_TAC] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC candle_fsn_atn_jet_shape THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MP_TAC
      (ISPECL
        [`n:num`;
         `value:((num#num)#(num#num))`;
         `gradient:((num#num)#(num#num))list`;
         `hessian:(((num#num)#(num#num))list)list`;
         `value_real:real`;
         `gradient_real:num->real`;
         `hessian_real:num->num->real`]
        candle_fsn_atn_hessian_contains) THEN
    ASM_REWRITE_TAC[]]);;

let candle_fsn_pi_half_jet_components = prove
 (`!(dimensions:((num#num)#(num#num))list).
     candle_q_dim_jet_contains_components (LENGTH dimensions)
       (candle_fs_first_to_q
         (candle_fs_first_make
           (candle_fs_interval_of_q candle_q_pi_half_interval)
           (candle_fs_interval_zeros dimensions))
         (candle_fs_interval_zero_matrix dimensions dimensions))
       (pi / &2) (\i. &0) (\i j. &0)`,
  GEN_TAC THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [MATCH_ACCEPT_TAC candle_fsn_pi_half_jet_shape;
    REWRITE_TAC[candle_fs_first_make_def;
                candle_fs_first_value_def; FST] THEN
    MATCH_MP_TAC candle_fs_interval_of_q_sound THEN
    MESON_TAC[candle_q_pi_half_interval_sound];
    REWRITE_TAC[candle_fs_first_make_def;
                candle_fs_first_gradient_def; SND] THEN
    ACCEPT_TAC
      (SPEC `dimensions:((num#num)#(num#num))list`
        candle_fs_interval_zeros_contains);
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (SPECL
        [`dimensions:((num#num)#(num#num))list`;
         `dimensions:((num#num)#(num#num))list`]
        candle_fs_interval_zero_matrix_contains)]);;

(* The nonlinear Hessian is formed from the whole-box value, gradient, and  *)
(* Hessian enclosures.  Expose that fact once at the analytic-expression     *)
(* level; both the center proof and the universal box proof reuse it.        *)

let candle_fsn_result_inv_analytic_hessian_contains = prove
 (`!center_e box_e target_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_erase_sqrt_certificates target_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_q_interval_not_zero
       (candle_fs_interval_to_q (candle_fs_result_value_bound result)) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_inv_hessian
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
             (Candle_analytic_inv target_e))
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let components_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `target_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates target_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`]) in
  let data_shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`;
      `result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list`;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ invariant_th domain_th) in
  let value_th,rest = CONJ_PAIR components_th in
  let gradient_th,hessian_th = CONJ_PAIR rest in
  let gradient_length_th,matrix_shape_th = CONJ_PAIR data_shape_th in
  let hessian_length_th,hessian_rows_th = CONJ_PAIR matrix_shape_th in
  let result_rule = ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_value_bound
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_gradient_bounds
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_hessian
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) target_e`;
      `(\di. candle_analytic_d di
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->num->real`]
     candle_fsn_inv_hessian_contains in
  let result_premises = end_itlist CONJ
     [gradient_length_th; hessian_length_th; hessian_rows_th;
      ASSUME
       `candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_result_value_bound
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`;
      value_th; gradient_th; hessian_th] in
  let result_th = MATCH_MP (BETA_RULE result_rule) result_premises in
  REWRITE_TAC[candle_analytic_dd_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  ACCEPT_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) result_th));;

let candle_fsn_result_inv_analytic_center_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_q_interval_not_zero
       (candle_fs_interval_to_q
         (candle_fs_first_value (candle_fs_result_center result))) /\
     candle_q_interval_not_zero
       (candle_fs_interval_to_q (candle_fs_result_value_bound result))
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_inv (candle_fs_result_center result))
         (candle_fsn_inv_hessian
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
       (Candle_analytic_inv center_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
   `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let premises_th = CONJ invariant_th domain_th in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_data_shape_th =
    REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th in
  let center_gradient_length_th = CONJUNCT1 center_data_shape_th in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  let proxy_gradient_length_th,proxy_matrix_shape_th =
    CONJ_PAIR proxy_data_shape_th in
  let proxy_hessian_length_th,proxy_hessian_rows_th =
    CONJ_PAIR proxy_matrix_shape_th in
  let center_value_th = MATCH_MP
    (instance candle_fs_result_analytic_center_value_contains)
    premises_th in
  let center_gradient_th = MATCH_MP
    (instance candle_fs_result_analytic_center_gradient_contains)
    premises_th in
  let center_first_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_center
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e`;
      `(\di. candle_analytic_d di
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->real`]
     candle_fsn_first_inv_contains))
   (end_itlist CONJ
     [ASSUME
       `candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_first_value
             (candle_fs_result_center
               (result:
                 bool#
                 (((num#num)#(num#num))#((num#num)#(num#num))list)#
                 ((num#num)#(num#num))#
                 ((num#num)#(num#num))list#
                 (((num#num)#(num#num))list)list))))`;
      center_value_th; center_gradient_th]) in
  let center_domain_th = MATCH_MP candle_q_box_m_cell_domain
   (CONJ
     (ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`)
     (ASSUME `candle_q_box_valid_list boxes`)) in
  let center_in_box_th = MATCH_MP y_in_domain center_domain_th in
  let center_hessian_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `center_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`;
      `(candle_q_box_center_vector boxes : real^N)`]
     candle_fsn_result_inv_analytic_hessian_contains)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates center_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_result_value_bound
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`;
      center_in_box_th]) in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_first_to_q_shape;
                candle_fsn_first_inv_gradient_length] THEN
    CONJ_TAC THENL
     [ACCEPT_TAC center_gradient_length_th;
      MATCH_MP_TAC candle_fsn_inv_hessian_shape THEN
      ACCEPT_TAC proxy_data_shape_th];
    ACCEPT_TAC (CONJUNCT1 center_first_th);
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV) (CONJUNCT2 center_first_th));
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE[candle_analytic_dd_def] center_hessian_th))]);;

let candle_fsn_result_inv_analytic_center_shape = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_inv (candle_fs_result_center result))
         (candle_fsn_inv_hessian
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let premises_th = CONJ
    (ASSUME
      `candle_q_dim_taylor_model_result_analytic_invariant
        (type_witness:real^N) boxes (candle_fs_result_to_q result)
        center_e box_e`)
    (ASSUME
      `candle_fs_result_domain
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`) in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_gradient_length_th = CONJUNCT1
    (REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th) in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_inv_gradient_length] THEN
  CONJ_TAC THENL
   [ACCEPT_TAC center_gradient_length_th;
    MATCH_MP_TAC candle_fsn_inv_hessian_shape THEN
    ACCEPT_TAC proxy_data_shape_th]);;

let candle_fsn_result_inv_analytic_box_hessian_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_q_interval_not_zero
       (candle_fs_interval_to_q (candle_fs_result_value_bound result)) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_inv_hessian
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim (Candle_analytic_inv box_e)) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let raw_hessian_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fsn_result_inv_analytic_hessian_contains)
   (end_itlist CONJ
     [REFL `candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_result_value_bound
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`;
      point_th]) in
  let components_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [REFL `candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th; point_th]) in
  let value_th = CONJUNCT1 components_th in
  let regular_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_box_regular)
   (CONJ invariant_th (CONJ domain_th point_th)) in
  let nonzero_th = MATCH_MP candle_q_interval_not_zero_contains_nonzero
   (CONJ
     (ASSUME
       `candle_q_interval_not_zero
         (candle_fs_interval_to_q
           (candle_fs_result_value_bound
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`)
     (REWRITE_RULE[GSYM candle_fs_interval_to_q_contains] value_th)) in
  MATCH_MP_TAC candle_fs_analytic_hessian_flyspeck_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_regular_at_def] THEN
    ACCEPT_TAC (CONJ regular_th nonzero_th);
    ACCEPT_TAC raw_hessian_th]);;

let candle_fsn_result_inv_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fsn_result_inv
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           result))
       (Candle_analytic_inv center_e) (Candle_analytic_inv box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_fsn_result_inv_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "input_domain")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_inv_domain")
          (LABEL_TAC "proxy_inv_domain"))) THEN
    USE_THEN "input_domain" ASSUME_TAC THEN
    USE_THEN "input_invariant"
     (fun input_invariant_th ->
        let enabled_th = MATCH_MP
         (REWRITE_RULE
           [candle_q_dim_taylor_model_result_analytic_invariant_def;
            candle_fs_result_to_q_domain]
           input_invariant_th)
         (ASSUME
           `candle_fs_result_domain
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)`) in
        let center_regular_th,rest1 = CONJ_PAIR enabled_th in
        let box_regular_all_th,_ = CONJ_PAIR rest1 in
        EVERY
         [candle_fsa_label_instantiated "center_regular"
            center_regular_th;
          candle_fsa_label_instantiated "box_regular_all"
            box_regular_all_th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [USE_THEN "center_regular" ACCEPT_TAC;
        MATCH_MP_TAC candle_q_interval_not_zero_contains_nonzero THEN
        EXISTS_TAC
         `candle_fs_interval_to_q
           (candle_fs_first_value
             (candle_fs_result_center
               (result:
                 bool#
                 (((num#num)#(num#num))#((num#num)#(num#num))list)#
                 ((num#num)#(num#num))#
                 ((num#num)#(num#num))list#
                 (((num#num)#(num#num))list)list)))` THEN
        CONJ_TAC THENL
         [USE_THEN "center_inv_domain" ACCEPT_TAC;
          REWRITE_TAC[candle_fs_interval_to_q_contains] THEN
          MP_TAC
           (ISPECL
             [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
              `boxes:(((num#num)#num)#((num#num)#num))list`;
              `result:
                bool#
                (((num#num)#(num#num))#((num#num)#(num#num))list)#
                ((num#num)#(num#num))#
                ((num#num)#(num#num))list#
                (((num#num)#(num#num))list)list`;
              `type_witness:real^N`]
             candle_fs_result_analytic_center_value_contains) THEN
          ASM_REWRITE_TAC[]]];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [USE_THEN "box_regular_all"
         (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC candle_q_interval_not_zero_contains_nonzero THEN
        EXISTS_TAC
         `candle_fs_interval_to_q
           (candle_fs_result_value_bound
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list))` THEN
        CONJ_TAC THENL
         [USE_THEN "proxy_inv_domain" ACCEPT_TAC;
          REWRITE_TAC[candle_fs_interval_to_q_contains] THEN
          MP_TAC
           (ISPECL
             [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
              `box_e:candle_analytic_expr`;
              `boxes:(((num#num)#num)#((num#num)#num))list`;
              `result:
                bool#
                (((num#num)#(num#num))#((num#num)#(num#num))list)#
                ((num#num)#(num#num))#
                ((num#num)#(num#num))list#
                (((num#num)#(num#num))list)list`;
              `type_witness:real^N`; `p:real^N`]
             candle_fs_result_analytic_proxy_target_components) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[];
            MESON_TAC[]]]];
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_inv_analytic_center_shape) THEN
      ASM_REWRITE_TAC[];
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_inv_analytic_center_contains) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`; `p:real^N`]
         candle_fsn_result_inv_analytic_box_hessian_contains) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_fsn_result_atn_analytic_hessian_contains = prove
 (`!center_e box_e target_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_erase_sqrt_certificates target_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_atn_domain (candle_fs_result_value_bound result) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_atn_hessian
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
             (Candle_analytic_atn target_e))
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let components_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `target_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates target_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`]) in
  let data_shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ invariant_th domain_th) in
  let value_th,rest = CONJ_PAIR components_th in
  let gradient_th,hessian_th = CONJ_PAIR rest in
  let gradient_length_th,matrix_shape_th = CONJ_PAIR data_shape_th in
  let hessian_length_th,hessian_rows_th = CONJ_PAIR matrix_shape_th in
  let result_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_value_bound
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_gradient_bounds
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_fs_result_hessian
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) target_e`;
      `(\di. candle_analytic_d di
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->real`;
      `(\di dj. candle_analytic_dd di dj
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
        target_e):num->num->real`]
     candle_fsn_atn_hessian_contains))
   (end_itlist CONJ
     [gradient_length_th; hessian_length_th; hessian_rows_th;
      ASSUME
       `candle_fsn_atn_domain
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      value_th; gradient_th; hessian_th]) in
  REWRITE_TAC[candle_analytic_dd_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  ACCEPT_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) result_th));;

let candle_fsn_result_atn_analytic_center_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_atn_domain
       (candle_fs_first_value (candle_fs_result_center result)) /\
     candle_fsn_atn_domain (candle_fs_result_value_bound result)
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_atn (candle_fs_result_center result))
         (candle_fsn_atn_hessian
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
       (Candle_analytic_atn center_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let premises_th = CONJ invariant_th domain_th in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_gradient_length_th = CONJUNCT1
    (REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th) in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  let center_value_th = MATCH_MP
    (instance candle_fs_result_analytic_center_value_contains)
    premises_th in
  let center_gradient_th = MATCH_MP
    (instance candle_fs_result_analytic_center_gradient_contains)
    premises_th in
  let center_first_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_fs_result_center
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e`;
      `(\di. candle_analytic_d di
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->real`]
     candle_fsn_first_atn_contains))
   (end_itlist CONJ
     [ASSUME
       `candle_fsn_atn_domain
         (candle_fs_first_value
           (candle_fs_result_center
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`;
      center_value_th; center_gradient_th]) in
  let center_domain_th = MATCH_MP candle_q_box_m_cell_domain
   (CONJ
     (ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`)
     (ASSUME `candle_q_box_valid_list boxes`)) in
  let center_in_box_th = MATCH_MP y_in_domain center_domain_th in
  let center_hessian_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `center_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`;
      `(candle_q_box_center_vector boxes : real^N)`]
     candle_fsn_result_atn_analytic_hessian_contains)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates center_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_fsn_atn_domain
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      center_in_box_th]) in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_first_to_q_shape;
                candle_fsn_first_atn_gradient_length] THEN
    CONJ_TAC THENL
     [ACCEPT_TAC center_gradient_length_th;
      MATCH_MP_TAC candle_fsn_atn_hessian_shape THEN
      ACCEPT_TAC proxy_data_shape_th];
    ACCEPT_TAC (CONJUNCT1 center_first_th);
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV) (CONJUNCT2 center_first_th));
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE[candle_analytic_dd_def] center_hessian_th))]);;

let candle_fsn_result_atn_analytic_center_shape = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_atn (candle_fs_result_center result))
         (candle_fsn_atn_hessian
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let premises_th = CONJ
    (ASSUME
      `candle_q_dim_taylor_model_result_analytic_invariant
        (type_witness:real^N) boxes (candle_fs_result_to_q result)
        center_e box_e`)
    (ASSUME
      `candle_fs_result_domain
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`) in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_gradient_length_th = CONJUNCT1
    (REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th) in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_atn_gradient_length] THEN
  CONJ_TAC THENL
   [ACCEPT_TAC center_gradient_length_th;
    MATCH_MP_TAC candle_fsn_atn_hessian_shape THEN
    ACCEPT_TAC proxy_data_shape_th]);;

let candle_fsn_result_atn_analytic_box_hessian_contains = prove
 (`!center_e box_e boxes result (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_atn_domain (candle_fs_result_value_bound result) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_atn_hessian
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim (Candle_analytic_atn box_e)) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let raw_hessian_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fsn_result_atn_analytic_hessian_contains)
   (end_itlist CONJ
     [REFL `candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_fsn_atn_domain
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      point_th]) in
  let regular_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_box_regular)
   (CONJ invariant_th (CONJ domain_th point_th)) in
  MATCH_MP_TAC candle_fs_analytic_hessian_flyspeck_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_regular_at_def] THEN
    ACCEPT_TAC regular_th;
    ACCEPT_TAC raw_hessian_th]);;

let candle_fsn_result_atn_analytic_invariant = prove
 (`!center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fsn_result_atn
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           result))
       (Candle_analytic_atn center_e) (Candle_analytic_atn box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_fsn_result_atn_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "input_domain")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_atn_domain")
          (LABEL_TAC "proxy_atn_domain"))) THEN
    USE_THEN "input_domain" ASSUME_TAC THEN
    USE_THEN "input_invariant"
     (fun input_invariant_th ->
        let enabled_th = MATCH_MP
         (REWRITE_RULE
           [candle_q_dim_taylor_model_result_analytic_invariant_def;
            candle_fs_result_to_q_domain]
           input_invariant_th)
         (ASSUME
           `candle_fs_result_domain
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)`) in
        let center_regular_th,rest1 = CONJ_PAIR enabled_th in
        let box_regular_all_th,_ = CONJ_PAIR rest1 in
        EVERY
         [candle_fsa_label_instantiated "center_regular"
            center_regular_th;
          candle_fsa_label_instantiated "box_regular_all"
            box_regular_all_th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "center_regular" ACCEPT_TAC;
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      USE_THEN "box_regular_all"
       (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
      ASM_REWRITE_TAC[];
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_atn_analytic_center_shape) THEN
      ASM_REWRITE_TAC[];
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_atn_analytic_center_contains) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      MP_TAC
       (ISPECL
         [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`; `p:real^N`]
         candle_fsn_result_atn_analytic_box_hessian_contains) THEN
      ASM_REWRITE_TAC[]]]);;

let candle_fsn_result_pi_half_analytic_invariant = prove
 (`!boxes dimensions (type_witness:real^N).
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     LENGTH dimensions = dimindex (:N)
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fsn_result_pi_half
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           dimensions))
       Candle_analytic_pi_half Candle_analytic_pi_half`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_fsn_result_pi_half_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def];
      REWRITE_TAC[candle_analytic_regular_at_def];
      MP_TAC
       (SPEC `dimensions:((num#num)#(num#num))list`
         candle_fsn_pi_half_jet_shape) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[candle_q_dim_analytic_contains_def;
                  candle_analytic_value_def;
                  candle_analytic_d_def;
                  candle_analytic_dd_def] THEN
      MP_TAC
       (SPEC `dimensions:((num#num)#(num#num))list`
         candle_fsn_pi_half_jet_components) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC candle_fs_analytic_hessian_flyspeck_contains THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[candle_analytic_valid_dim_def];
        REWRITE_TAC[candle_analytic_regular_at_def];
        REWRITE_TAC[candle_analytic_dd_def] THEN
        CONV_TAC (DEPTH_CONV BETA_CONV) THEN
        MP_TAC
         (SPECL
           [`dimensions:((num#num)#(num#num))list`;
            `dimensions:((num#num)#(num#num))list`]
           candle_fs_interval_zero_matrix_contains) THEN
        ASM_REWRITE_TAC[]]]]);;

let candle_fsn_result_sqrt_analytic_hessian_contains = prove
 (`!lp ln ld up un ud center_e box_e target_e boxes result
      (type_witness:real^N) (p:real^N).
     candle_analytic_erase_sqrt_certificates target_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_sqrt_domain
       (candle_analytic_sqrt_interval lp ln ld up un ud)
       (candle_fs_result_value_bound result) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_sqrt_hessian
         (candle_analytic_sqrt_interval lp ln ld up un ud)
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. candle_analytic_dd di dj
             (list_of_seq (\k. p$(k + 1)) (dimindex (:N)))
             (Candle_analytic_sqrt lp ln ld up un ud target_e))
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let components_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `target_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates target_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `(p:real^N) IN interval
         [candle_q_box_lower_vector boxes,
          candle_q_box_upper_vector boxes]`]) in
  let data_shape_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`]
     candle_fs_result_analytic_proxy_data_shape)
   (CONJ invariant_th domain_th) in
  let value_th,rest = CONJ_PAIR components_th in
  let gradient_th,hessian_th = CONJ_PAIR rest in
  let gradient_length_th,matrix_shape_th = CONJ_PAIR data_shape_th in
  let hessian_length_th,hessian_rows_th = CONJ_PAIR matrix_shape_th in
  let result_rule = BETA_RULE (ISPECL
    [`dimindex (:N)`;
     `candle_analytic_sqrt_interval
       (lp:num) (ln:num) (ld:num) (up:num) (un:num) (ud:num)`;
     `candle_fs_result_value_bound
       (result:
         bool#
         (((num#num)#(num#num))#((num#num)#(num#num))list)#
         ((num#num)#(num#num))#
         ((num#num)#(num#num))list#
         (((num#num)#(num#num))list)list)`;
     `candle_fs_result_gradient_bounds
       (result:
         bool#
         (((num#num)#(num#num))#((num#num)#(num#num))list)#
         ((num#num)#(num#num))#
         ((num#num)#(num#num))list#
         (((num#num)#(num#num))list)list)`;
     `candle_fs_result_hessian
       (result:
         bool#
         (((num#num)#(num#num))#((num#num)#(num#num))list)#
         ((num#num)#(num#num))#
         ((num#num)#(num#num))list#
         (((num#num)#(num#num))list)list)`;
     `candle_analytic_value
       (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) target_e`;
     `(\di. candle_analytic_d di
       (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
       target_e):num->real`;
     `(\di dj. candle_analytic_dd di dj
       (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
       target_e):num->num->real`]
    candle_fsn_sqrt_hessian_contains) in
  let result_th = MATCH_MP result_rule
   (end_itlist CONJ
     [gradient_length_th; hessian_length_th; hessian_rows_th;
      ASSUME
       `candle_fsn_sqrt_domain
         (candle_analytic_sqrt_interval
           (lp:num) (ln:num) (ld:num) (up:num) (un:num) (ud:num))
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      value_th; gradient_th; hessian_th]) in
  REWRITE_TAC[candle_analytic_dd_def] THEN
  CONV_TAC (DEPTH_CONV BETA_CONV) THEN
  ACCEPT_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) result_th));;

let candle_fsn_result_sqrt_analytic_center_contains = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes result (type_witness:real^N).
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_sqrt_domain
       (candle_analytic_sqrt_interval clp cln cld cup cun cud)
       (candle_fs_first_value (candle_fs_result_center result)) /\
     candle_fsn_sqrt_domain
       (candle_analytic_sqrt_interval blp bln bld bup bun bud)
       (candle_fs_result_value_bound result)
     ==>
     candle_q_dim_analytic_contains (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_sqrt
           (candle_analytic_sqrt_interval clp cln cld cup cun cud)
           (candle_fs_result_center result))
         (candle_fsn_sqrt_hessian
           (candle_analytic_sqrt_interval blp bln bld bup bun bud)
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))
       (list_of_seq
         (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
         (dimindex (:N)))
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let premises_th = CONJ invariant_th domain_th in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_gradient_length_th = CONJUNCT1
    (REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th) in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  let center_value_th = MATCH_MP
    (instance candle_fs_result_analytic_center_value_contains)
    premises_th in
  let center_gradient_th = MATCH_MP
    (instance candle_fs_result_analytic_center_gradient_contains)
    premises_th in
  let center_first_th = MATCH_MP
   (BETA_RULE (ISPECL
     [`dimindex (:N)`;
      `candle_analytic_sqrt_interval
        (clp:num) (cln:num) (cld:num) (cup:num) (cun:num) (cud:num)`;
      `candle_fs_result_center
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e`;
      `(\di. candle_analytic_d di
        (list_of_seq
          (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
          (dimindex (:N))) center_e):num->real`]
     candle_fsn_first_sqrt_contains))
   (end_itlist CONJ
     [ASSUME
       `candle_fsn_sqrt_domain
         (candle_analytic_sqrt_interval
           (clp:num) (cln:num) (cld:num) (cup:num) (cun:num) (cud:num))
         (candle_fs_first_value
           (candle_fs_result_center
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)))`;
      center_value_th; center_gradient_th]) in
  let center_domain_th = MATCH_MP candle_q_box_m_cell_domain
   (CONJ
     (ASSUME
       `LENGTH (boxes:(((num#num)#num)#((num#num)#num))list) =
        dimindex (:N)`)
     (ASSUME `candle_q_box_valid_list boxes`)) in
  let center_in_box_th = MATCH_MP y_in_domain center_domain_th in
  let center_hessian_th = MATCH_MP
   (ISPECL
     [`blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
      `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `center_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`;
      `(candle_q_box_center_vector boxes : real^N)`]
     candle_fsn_result_sqrt_analytic_hessian_contains)
   (end_itlist CONJ
     [ASSUME
       `candle_analytic_erase_sqrt_certificates center_e =
        candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_fsn_sqrt_domain
         (candle_analytic_sqrt_interval
           (blp:num) (bln:num) (bld:num) (bup:num) (bun:num) (bud:num))
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      center_in_box_th]) in
  REWRITE_TAC[candle_q_dim_analytic_contains_def;
              candle_analytic_value_def;
              candle_analytic_d_def;
              candle_analytic_dd_def] THEN
  MATCH_MP_TAC candle_fs_first_components_from_data THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[candle_fs_first_to_q_shape;
                candle_fsn_first_sqrt_gradient_length] THEN
    CONJ_TAC THENL
     [ACCEPT_TAC center_gradient_length_th;
      MATCH_MP_TAC candle_fsn_sqrt_hessian_shape THEN
      ACCEPT_TAC proxy_data_shape_th];
    ACCEPT_TAC (CONJUNCT1 center_first_th);
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV) (CONJUNCT2 center_first_th));
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ACCEPT_TAC
      (CONV_RULE (DEPTH_CONV BETA_CONV)
        (REWRITE_RULE[candle_analytic_dd_def] center_hessian_th))]);;

let candle_fsn_result_sqrt_analytic_center_shape = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes result (type_witness:real^N).
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result
     ==>
     candle_q_dim_jet_shape (dimindex (:N))
       (candle_fs_first_to_q
         (candle_fsn_first_sqrt
           (candle_analytic_sqrt_interval clp cln cld cup cun cud)
           (candle_fs_result_center result))
         (candle_fsn_sqrt_hessian
           (candle_analytic_sqrt_interval blp bln bld bup bun bud)
           (candle_fs_result_value_bound result)
           (candle_fs_result_gradient_bounds result)
           (candle_fs_result_hessian result)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let premises_th = CONJ
    (ASSUME
      `candle_q_dim_taylor_model_result_analytic_invariant
        (type_witness:real^N) boxes (candle_fs_result_to_q result)
        center_e box_e`)
    (ASSUME
      `candle_fs_result_domain
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`) in
  let instance theorem = ISPECL
    [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
     `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
     `type_witness:real^N`] theorem in
  let center_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_center_shape) premises_th in
  let center_gradient_length_th = CONJUNCT1
    (REWRITE_RULE[candle_fs_first_to_q_shape] center_shape_th) in
  let proxy_data_shape_th = MATCH_MP
    (instance candle_fs_result_analytic_proxy_data_shape) premises_th in
  REWRITE_TAC[candle_fs_first_to_q_shape;
              candle_fsn_first_sqrt_gradient_length] THEN
  CONJ_TAC THENL
   [ACCEPT_TAC center_gradient_length_th;
    MATCH_MP_TAC candle_fsn_sqrt_hessian_shape THEN
    ACCEPT_TAC proxy_data_shape_th]);;

let candle_fsn_result_sqrt_analytic_box_hessian_contains = prove
 (`!lp ln ld up un ud center_e box_e boxes result
      (type_witness:real^N) (p:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e /\
     candle_fs_result_domain result /\
     candle_fsn_sqrt_domain
       (candle_analytic_sqrt_interval lp ln ld up un ud)
       (candle_fs_result_value_bound result) /\
     p IN interval
       [candle_q_box_lower_vector boxes,
        candle_q_box_upper_vector boxes]
     ==>
     ALL2 (ALL2 candle_fs_interval_contains)
       (candle_fsn_sqrt_hessian
         (candle_analytic_sqrt_interval lp ln ld up un ud)
         (candle_fs_result_value_bound result)
         (candle_fs_result_gradient_bounds result)
         (candle_fs_result_hessian result))
       (list_of_seq
         (\di. list_of_seq
           (\dj. partial2 (dj + 1) (di + 1)
             (candle_analytic_denote_dim
               (Candle_analytic_sqrt lp ln ld up un ud box_e)) p)
           (dimindex (:N)))
         (dimindex (:N)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let result_term =
   `result:
      bool#
      (((num#num)#(num#num))#((num#num)#(num#num))list)#
      ((num#num)#(num#num))#
      ((num#num)#(num#num))list#
      (((num#num)#(num#num))list)list` in
  let invariant_th = ASSUME
    `candle_q_dim_taylor_model_result_analytic_invariant
      (type_witness:real^N) boxes (candle_fs_result_to_q result)
      center_e box_e` in
  let domain_th = ASSUME
    `candle_fs_result_domain
      (result:
        bool#
        (((num#num)#(num#num))#((num#num)#(num#num))list)#
        ((num#num)#(num#num))#
        ((num#num)#(num#num))list#
        (((num#num)#(num#num))list)list)` in
  let point_th = ASSUME
    `(p:real^N) IN interval
      [candle_q_box_lower_vector boxes,
       candle_q_box_upper_vector boxes]` in
  let raw_hessian_th = MATCH_MP
   (ISPECL
     [`lp:num`; `ln:num`; `ld:num`; `up:num`; `un:num`; `ud:num`;
      `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fsn_result_sqrt_analytic_hessian_contains)
   (end_itlist CONJ
     [REFL `candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th;
      ASSUME
       `candle_fsn_sqrt_domain
         (candle_analytic_sqrt_interval
           (lp:num) (ln:num) (ld:num) (up:num) (un:num) (ud:num))
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`;
      point_th]) in
  let components_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_proxy_target_components)
   (end_itlist CONJ
     [REFL `candle_analytic_erase_sqrt_certificates box_e`;
      invariant_th; domain_th; point_th]) in
  let value_th = CONJUNCT1 components_th in
  let regular_th = MATCH_MP
   (ISPECL
     [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
      `boxes:(((num#num)#num)#((num#num)#num))list`; result_term;
      `type_witness:real^N`; `p:real^N`]
     candle_fs_result_analytic_box_regular)
   (CONJ invariant_th (CONJ domain_th point_th)) in
  let positive_th = MATCH_MP
   (ISPECL
     [`candle_analytic_sqrt_interval
       (lp:num) (ln:num) (ld:num) (up:num) (un:num) (ud:num)`;
      `candle_fs_result_value_bound
        (result:
          bool#
          (((num#num)#(num#num))#((num#num)#(num#num))list)#
          ((num#num)#(num#num))#
          ((num#num)#(num#num))list#
          (((num#num)#(num#num))list)list)`;
      `candle_analytic_value
        (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N))) box_e`]
     candle_fsn_sqrt_domain_value_positive)
   (CONJ
     (ASSUME
       `candle_fsn_sqrt_domain
         (candle_analytic_sqrt_interval
           (lp:num) (ln:num) (ld:num) (up:num) (un:num) (ud:num))
         (candle_fs_result_value_bound
           (result:
             bool#
             (((num#num)#(num#num))#((num#num)#(num#num))list)#
             ((num#num)#(num#num))#
             ((num#num)#(num#num))list#
             (((num#num)#(num#num))list)list))`)
     value_th) in
  MATCH_MP_TAC candle_fs_analytic_hessian_flyspeck_contains THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    REWRITE_TAC[candle_analytic_regular_at_def] THEN
    ACCEPT_TAC (CONJ regular_th positive_th);
    ACCEPT_TAC raw_hessian_th]);;

let candle_fsn_result_sqrt_analytic_invariant = prove
 (`!clp cln cld cup cun cud blp bln bld bup bun bud
      center_e box_e boxes result (type_witness:real^N).
     candle_analytic_valid_dim (dimindex (:N)) box_e /\
     candle_analytic_erase_sqrt_certificates center_e =
       candle_analytic_erase_sqrt_certificates box_e /\
     LENGTH boxes = dimindex (:N) /\
     candle_q_box_valid_list boxes /\
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes (candle_fs_result_to_q result) center_e box_e
     ==>
     candle_q_dim_taylor_model_result_analytic_invariant
       type_witness boxes
       (candle_fs_result_to_q
         (candle_fsn_result_sqrt
           (candle_fs_list_of_q
             (candle_q_fixed_list_round_upper
               (candle_q_radius_list boxes)))
           (candle_analytic_sqrt_interval clp cln cld cup cun cud)
           (candle_analytic_sqrt_interval blp bln bld bup bun bud)
           result))
       (Candle_analytic_sqrt clp cln cld cup cun cud center_e)
       (Candle_analytic_sqrt blp bln bld bup bun bud box_e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  POP_ASSUM (LABEL_TAC "input_invariant") THEN
  REWRITE_TAC[candle_fsn_result_sqrt_def] THEN
  MATCH_MP_TAC candle_fs_result_complete_analytic_invariant THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[candle_analytic_valid_dim_def];
    ASM_REWRITE_TAC[candle_analytic_erase_sqrt_certificates_def];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    DISCH_THEN
      (CONJUNCTS_THEN2 (LABEL_TAC "input_domain")
        (CONJUNCTS_THEN2 (LABEL_TAC "center_sqrt_domain")
          (LABEL_TAC "proxy_sqrt_domain"))) THEN
    USE_THEN "input_domain" ASSUME_TAC THEN
    USE_THEN "input_invariant"
     (fun input_invariant_th ->
        let enabled_th = MATCH_MP
         (REWRITE_RULE
           [candle_q_dim_taylor_model_result_analytic_invariant_def;
            candle_fs_result_to_q_domain]
           input_invariant_th)
         (ASSUME
           `candle_fs_result_domain
             (result:
               bool#
               (((num#num)#(num#num))#((num#num)#(num#num))list)#
               ((num#num)#(num#num))#
               ((num#num)#(num#num))list#
               (((num#num)#(num#num))list)list)`) in
        let center_regular_th,rest1 = CONJ_PAIR enabled_th in
        let box_regular_all_th,_ = CONJ_PAIR rest1 in
        EVERY
         [candle_fsa_label_instantiated "center_regular"
            center_regular_th;
          candle_fsa_label_instantiated "box_regular_all"
            box_regular_all_th]) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [USE_THEN "center_regular" ACCEPT_TAC;
        MATCH_MP_TAC
         (ISPECL
           [`candle_analytic_sqrt_interval
             (clp:num) (cln:num) (cld:num)
             (cup:num) (cun:num) (cud:num)`;
            `candle_fs_first_value
              (candle_fs_result_center
                (result:
                  bool#
                  (((num#num)#(num#num))#((num#num)#(num#num))list)#
                  ((num#num)#(num#num))#
                  ((num#num)#(num#num))list#
                  (((num#num)#(num#num))list)list))`;
            `candle_analytic_value
              (list_of_seq
                (\k. (candle_q_box_center_vector boxes : real^N)$(k + 1))
                (dimindex (:N))) center_e`]
           candle_fsn_sqrt_domain_value_positive) THEN
        CONJ_TAC THENL
         [USE_THEN "center_sqrt_domain" ACCEPT_TAC;
          MP_TAC
           (ISPECL
             [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
              `boxes:(((num#num)#num)#((num#num)#num))list`;
              `result:
                bool#
                (((num#num)#(num#num))#((num#num)#(num#num))list)#
                ((num#num)#(num#num))#
                ((num#num)#(num#num))list#
                (((num#num)#(num#num))list)list`;
              `type_witness:real^N`]
             candle_fs_result_analytic_center_value_contains) THEN
          ASM_REWRITE_TAC[]]];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[candle_analytic_regular_at_def] THEN
      CONJ_TAC THENL
       [USE_THEN "box_regular_all"
         (fun th -> MATCH_MP_TAC (SPEC `p:real^N` th)) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC
         (ISPECL
           [`candle_analytic_sqrt_interval
             (blp:num) (bln:num) (bld:num)
             (bup:num) (bun:num) (bud:num)`;
            `candle_fs_result_value_bound
              (result:
                bool#
                (((num#num)#(num#num))#((num#num)#(num#num))list)#
                ((num#num)#(num#num))#
                ((num#num)#(num#num))list#
                (((num#num)#(num#num))list)list)`;
            `candle_analytic_value
              (list_of_seq (\k. (p:real^N)$(k + 1)) (dimindex (:N)))
              box_e`]
           candle_fsn_sqrt_domain_value_positive) THEN
        CONJ_TAC THENL
         [USE_THEN "proxy_sqrt_domain" ACCEPT_TAC;
          MP_TAC
           (ISPECL
             [`center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
              `box_e:candle_analytic_expr`;
              `boxes:(((num#num)#num)#((num#num)#num))list`;
              `result:
                bool#
                (((num#num)#(num#num))#((num#num)#(num#num))list)#
                ((num#num)#(num#num))#
                ((num#num)#(num#num))list#
                (((num#num)#(num#num))list)list`;
              `type_witness:real^N`; `p:real^N`]
             candle_fs_result_analytic_proxy_target_components) THEN
          ANTS_TAC THENL
           [ASM_REWRITE_TAC[];
            MESON_TAC[]]]];
      MP_TAC
       (ISPECL
         [`clp:num`; `cln:num`; `cld:num`; `cup:num`; `cun:num`; `cud:num`;
          `blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
          `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_sqrt_analytic_center_shape) THEN
      ASM_REWRITE_TAC[];
      MP_TAC
       (ISPECL
         [`clp:num`; `cln:num`; `cld:num`; `cup:num`; `cun:num`; `cud:num`;
          `blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
          `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`]
         candle_fsn_result_sqrt_analytic_center_contains) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
      MP_TAC
       (ISPECL
         [`blp:num`; `bln:num`; `bld:num`; `bup:num`; `bun:num`; `bud:num`;
          `center_e:candle_analytic_expr`; `box_e:candle_analytic_expr`;
          `boxes:(((num#num)#num)#((num#num)#num))list`;
          `result:
            bool#
            (((num#num)#(num#num))#((num#num)#(num#num))list)#
            ((num#num)#(num#num))#
            ((num#num)#(num#num))list#
            (((num#num)#(num#num))list)list`;
          `type_witness:real^N`; `p:real^N`]
         candle_fsn_result_sqrt_analytic_box_hessian_contains) THEN
      ASM_REWRITE_TAC[]]]);;

end;;
