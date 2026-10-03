(* ========================================================================== *)
(* Analytic invariant for the reflected fixed-nonlinear program.              *)
(*                                                                            *)
(* This file deliberately sits above the stable executable-correspondence and *)
(* scalar/shape soundness layer.  Keeping the changing operation proofs here  *)
(* lets development restart from the sealed nonlinear support checkpoint.     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_sound.ml";;

module Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_invariant = struct

open Candle_cv_analytic_expr_fixed_scale_sound;;
open Candle_cv_analytic_expr_fixed_scale_invariant;;
open Candle_cv_exact_interval_sqrt_certificate;;
open Candle_cv_analytic_dim_jet_sqrt;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_sound;;

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

end;;
