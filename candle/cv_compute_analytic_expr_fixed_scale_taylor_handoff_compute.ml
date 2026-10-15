(* ========================================================================== *)
(* Bounded fixed-scale Taylor handoff for already authenticated exact jets.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The analytic program still produces exact     *)
(* center and whole-box jets.  This small checker immediately rounds only the *)
(* components consumed by the final Taylor sum to a directed 10^-12 grid,    *)
(* preventing the denominator growth seen in the exact 6x6 accumulation.     *)
(* A companion soundness file must connect acceptance to the existing exact  *)
(* analytic-jet theorem before this may support a release claim.              *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_jet_check.ml";;

module Candle_cv_analytic_expr_fixed_scale_taylor_handoff_compute = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_whole_box_taylor;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_analytic_expr_program_compute;;
open Candle_cv_analytic_expr_jet_check;;

let marker stage =
  print_endline ("CANDLE_CV_MATAN_FS_HANDOFF_DEFINE " ^ stage);;
let _ = marker "begin";;

let candle_cv_matan_fs_scale_def = new_definition
 `candle_cv_matan_fs_scale = Cexp_num 1000000000000`;;

let candle_cv_matan_fs_scale_squared_def = new_definition
 `candle_cv_matan_fs_scale_squared =
    Cexp_mul candle_cv_matan_fs_scale candle_cv_matan_fs_scale`;;
let _ = marker "scale";;

let candle_cv_matan_fs_ceil_div_def = new_definition
 `candle_cv_matan_fs_ceil_div numerator denominator =
    Cexp_add (Cexp_div numerator denominator)
      (Cexp_if (Cexp_eq (Cexp_mod numerator denominator) (Cexp_num 0))
        (Cexp_num 0) (Cexp_num 1))`;;

let candle_cv_matan_fs_q_den_def = new_definition
 `candle_cv_matan_fs_q_den q = Cexp_add (Cexp_snd q) (Cexp_num 1)`;;
let _ = marker "division";;

(* Directed ceiling of [scale * q], retained as a signed natural pair. *)
let candle_cv_matan_fs_q_upper_def = new_definition
 `candle_cv_matan_fs_q_upper q =
    Cexp_if
      (Cexp_less (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
      (Cexp_pair (Cexp_num 0)
        (Cexp_div
          (Cexp_mul
            (Cexp_sub (Cexp_snd (Cexp_fst q)) (Cexp_fst (Cexp_fst q)))
            candle_cv_matan_fs_scale)
          (candle_cv_matan_fs_q_den q)))
      (Cexp_pair
        (candle_cv_matan_fs_ceil_div
          (Cexp_mul
            (Cexp_sub (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
            candle_cv_matan_fs_scale)
          (candle_cv_matan_fs_q_den q))
        (Cexp_num 0))`;;
let _ = marker "q-upper";;

let candle_cv_matan_fs_q_abs_upper_def = new_definition
 `candle_cv_matan_fs_q_abs_upper q =
    candle_cv_matan_fs_ceil_div
      (Cexp_mul
        (Cexp_if
          (Cexp_less (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
          (Cexp_sub (Cexp_snd (Cexp_fst q)) (Cexp_fst (Cexp_fst q)))
          (Cexp_sub (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q))))
        candle_cv_matan_fs_scale)
      (candle_cv_matan_fs_q_den q)`;;
let _ = marker "q-abs-upper";;

(* Each six-entry exact row is small enough to compute directly.  Round the *)
(* completed row product before the outer sum, which is the accumulation that *)
(* exhibited denominator growth on the genuine source.                       *)
let candle_cv_matan_fs_weighted_rows_upper_def = define
 `(candle_cv_matan_fs_weighted_rows_upper radii
      (Cexp_num n) row_lists = Cexp_num 0) /\
  (candle_cv_matan_fs_weighted_rows_upper radii
      (Cexp_pair weight weights) (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_matan_fs_weighted_rows_upper radii
      (Cexp_pair weight weights) (Cexp_pair interval_row row_tail) =
     Cexp_add
       (candle_cv_matan_fs_q_abs_upper
         (candle_cv_q_mul weight
           (candle_cv_q_dot_abs_upper radii interval_row)))
       (candle_cv_matan_fs_weighted_rows_upper radii weights row_tail))`;;
let _ = marker "weighted-rows-upper";;

let candle_cv_matan_fs_weighted_rows_upper_compute = prove
 (`!radii weights row_lists.
     candle_cv_matan_fs_weighted_rows_upper radii weights row_lists =
     Cexp_if (Cexp_ispair weights)
       (Cexp_if (Cexp_ispair row_lists)
         (Cexp_add
           (candle_cv_matan_fs_q_abs_upper
             (candle_cv_q_mul (Cexp_fst weights)
               (candle_cv_q_dot_abs_upper radii
                 (Cexp_fst row_lists))))
           (candle_cv_matan_fs_weighted_rows_upper radii
             (Cexp_snd weights) (Cexp_snd row_lists)))
         (Cexp_num 0))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `weights:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `row_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_matan_fs_weighted_rows_upper_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;
let _ = marker "weighted-rows-compute";;

let candle_cv_matan_fs_taylor_finish_def = new_definition
 `candle_cv_matan_fs_taylor_finish
      domain valid boxes center_value center_gradient box_hessian =
    let (radii:cval) = candle_cv_q_radius_list boxes in
    let (value:cval) =
      candle_cv_matan_fs_q_upper (Cexp_snd center_value) in
    let (gradient:cval) =
      candle_cv_matan_fs_q_abs_upper
        (candle_cv_q_dot_abs_upper radii center_gradient) in
    let (hessian:cval) =
      candle_cv_matan_fs_ceil_div
        (candle_cv_matan_fs_weighted_rows_upper radii radii box_hessian)
        (Cexp_num 2) in
    let (positive:cval) = Cexp_add gradient hessian in
    let (upper_positive:cval) = Cexp_add (Cexp_fst value) positive in
    Cexp_pair
      (Cexp_if domain
        (Cexp_if valid (Cexp_less upper_positive (Cexp_snd value))
          (Cexp_num 0))
        (Cexp_num 0))
      (Cexp_pair upper_positive (Cexp_snd value))`;;
let _ = marker "taylor-finish";;
let candle_cv_matan_fs_taylor_finish_compute =
  REWRITE_RULE[LET_DEF; LET_END_DEF]
    candle_cv_matan_fs_taylor_finish_def;;

let candle_cv_matan_fs_taylor_dual_check_def = new_definition
 `candle_cv_matan_fs_taylor_dual_check center_program box_program boxes =
    let (center_result:cval) =
      candle_cv_q_dim_analytic_program
        (candle_cv_q_center_environment_list boxes) center_program in
    let (box_result:cval) =
      candle_cv_q_dim_analytic_program boxes box_program in
    candle_cv_matan_fs_taylor_finish
      (candle_cv_bool_and
        (candle_cv_q_dim_analytic_result_domain center_result)
        (candle_cv_q_dim_analytic_result_domain box_result))
      (candle_cv_q_box_valid_list boxes) boxes
      (candle_cv_q_dim_jet_f
        (candle_cv_q_dim_analytic_result_jet center_result))
      (candle_cv_q_dim_jet_gradient
        (candle_cv_q_dim_analytic_result_jet center_result))
      (candle_cv_q_dim_jet_hessian
        (candle_cv_q_dim_analytic_result_jet box_result))`;;
let _ = marker "dual-check";;
let candle_cv_matan_fs_taylor_dual_check_compute =
  REWRITE_RULE[LET_DEF; LET_END_DEF]
    candle_cv_matan_fs_taylor_dual_check_def;;

let candle_cv_matan_fs_taylor_handoff_compute_eqs =
  candle_cv_q_dim_analytic_jet_compute_eqs @
  map SPEC_ALL
   [candle_cv_matan_fs_scale_def;
    candle_cv_matan_fs_scale_squared_def;
    candle_cv_matan_fs_ceil_div_def;
    candle_cv_matan_fs_q_den_def;
    candle_cv_matan_fs_q_upper_def;
    candle_cv_matan_fs_q_abs_upper_def;
    candle_cv_matan_fs_weighted_rows_upper_compute;
    candle_cv_matan_fs_taylor_finish_compute;
    candle_cv_matan_fs_taylor_dual_check_compute];;
let _ = marker "compute-equations";;

end;;
