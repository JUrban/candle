(* ========================================================================== *)
(* Reflected fixed-scale jets for the two Flyspeck angle polynomials.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  This is initially a       *)
(* Kernel.compute performance/equality discriminator.  The corresponding      *)
(* general containment theorems and authenticated compiled-program dispatch   *)
(* are required before this implementation can support a proof claim.         *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;

module Candle_cv_analytic_expr_fixed_scale_angle_polynomials_compute = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;

let candle_cv_fs_angle_six_def = new_definition
 `candle_cv_fs_angle_six a b c d e f =
    Cexp_pair a (Cexp_pair b (Cexp_pair c
      (Cexp_pair d (Cexp_pair e (Cexp_pair f (Cexp_num 0))))))`;;

let candle_cv_fs_angle_seven_def = new_definition
 `candle_cv_fs_angle_seven a b c d e f g =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_pair d
      (Cexp_pair e (Cexp_pair f (Cexp_pair g (Cexp_num 0)))))))`;;

let candle_cv_fs_angle_ten_def = new_definition
 `candle_cv_fs_angle_ten a b c d e f g h i j =
    Cexp_pair a (Cexp_pair b (Cexp_pair c (Cexp_pair d (Cexp_pair e
      (Cexp_pair f (Cexp_pair g (Cexp_pair h
        (Cexp_pair i (Cexp_pair j (Cexp_num 0))))))))))`;;

let candle_cv_fs_angle_interval_sum_def = define
 `(candle_cv_fs_angle_interval_sum (Cexp_num n) =
     candle_cv_fs_interval_zero) /\
  (candle_cv_fs_angle_interval_sum (Cexp_pair h t) =
     candle_cv_fs_interval_add h (candle_cv_fs_angle_interval_sum t))`;;

let candle_cv_fs_angle_interval_sum_compute = prove
 (`!items.
     candle_cv_fs_angle_interval_sum items =
     Cexp_if (Cexp_ispair items)
       (candle_cv_fs_interval_add (Cexp_fst items)
         (candle_cv_fs_angle_interval_sum (Cexp_snd items)))
       candle_cv_fs_interval_zero`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_angle_interval_sum_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_angle_interval_scale_def = new_definition
 `candle_cv_fs_angle_interval_scale factor value =
    Cexp_pair
      (candle_cv_fs_raw_scale factor (Cexp_fst value))
      (candle_cv_fs_raw_scale factor (Cexp_snd value))`;;

let candle_cv_fs_angle_interval_scale_neg_two_def = new_definition
 `candle_cv_fs_angle_interval_scale_neg_two value =
    candle_cv_fs_interval_neg
      (candle_cv_fs_angle_interval_scale (Cexp_num 2) value)`;;

let candle_cv_fs_angle_interval_mul_def = new_definition
 `candle_cv_fs_angle_interval_mul left right =
    candle_cv_fs_raw_interval_round candle_cv_fs_scale
      (candle_cv_fs_raw_interval_mul left right)`;;

let candle_cv_fs_angle_delta_value_def = new_definition
 `candle_cv_fs_angle_delta_value environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let l0 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six (candle_cv_fs_interval_neg x0) x1 x2
        (candle_cv_fs_interval_neg x3) x4 x5) in
    let l1 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0 (candle_cv_fs_interval_neg x1) x2 x3
        (candle_cv_fs_interval_neg x4) x5) in
    let l2 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0 x1 (candle_cv_fs_interval_neg x2) x3 x4
        (candle_cv_fs_interval_neg x5)) in
    let p03 = candle_cv_fs_angle_interval_mul x0 x3 in
    let p14 = candle_cv_fs_angle_interval_mul x1 x4 in
    let p25 = candle_cv_fs_angle_interval_mul x2 x5 in
    candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_seven
        (candle_cv_fs_angle_interval_mul p03 l0)
        (candle_cv_fs_angle_interval_mul p14 l1)
        (candle_cv_fs_angle_interval_mul p25 l2)
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_angle_interval_mul x1 x2) x3))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_angle_interval_mul x0 x2) x4))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_angle_interval_mul x0 x1) x5))
        (candle_cv_fs_interval_neg
          (candle_cv_fs_angle_interval_mul
            (candle_cv_fs_angle_interval_mul x3 x4) x5)))`;;

let candle_cv_fs_angle_delta_gradient_def = new_definition
 `candle_cv_fs_angle_delta_gradient environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let p00 = candle_cv_fs_angle_interval_mul x0 x0 in
    let p01 = candle_cv_fs_angle_interval_mul x0 x1 in
    let p02 = candle_cv_fs_angle_interval_mul x0 x2 in
    let p03 = candle_cv_fs_angle_interval_mul x0 x3 in
    let p04 = candle_cv_fs_angle_interval_mul x0 x4 in
    let p05 = candle_cv_fs_angle_interval_mul x0 x5 in
    let p11 = candle_cv_fs_angle_interval_mul x1 x1 in
    let p12 = candle_cv_fs_angle_interval_mul x1 x2 in
    let p13 = candle_cv_fs_angle_interval_mul x1 x3 in
    let p14 = candle_cv_fs_angle_interval_mul x1 x4 in
    let p15 = candle_cv_fs_angle_interval_mul x1 x5 in
    let p22 = candle_cv_fs_angle_interval_mul x2 x2 in
    let p23 = candle_cv_fs_angle_interval_mul x2 x3 in
    let p24 = candle_cv_fs_angle_interval_mul x2 x4 in
    let p25 = candle_cv_fs_angle_interval_mul x2 x5 in
    let p33 = candle_cv_fs_angle_interval_mul x3 x3 in
    let p34 = candle_cv_fs_angle_interval_mul x3 x4 in
    let p35 = candle_cv_fs_angle_interval_mul x3 x5 in
    let p44 = candle_cv_fs_angle_interval_mul x4 x4 in
    let p45 = candle_cv_fs_angle_interval_mul x4 x5 in
    let p55 = candle_cv_fs_angle_interval_mul x5 x5 in
    candle_cv_fs_angle_six
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten
          (candle_cv_fs_angle_interval_scale_neg_two p03) p13 p14
          (candle_cv_fs_interval_neg p15) p23
          (candle_cv_fs_interval_neg p24) p25
          (candle_cv_fs_interval_neg p33) p34 p35))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten p03 p04
          (candle_cv_fs_interval_neg p05)
          (candle_cv_fs_angle_interval_scale_neg_two p14)
          (candle_cv_fs_interval_neg p23) p24 p25 p34
          (candle_cv_fs_interval_neg p44) p45))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten p03 (candle_cv_fs_interval_neg p04) p05
          (candle_cv_fs_interval_neg p13) p14 p15
          (candle_cv_fs_angle_interval_scale_neg_two p25) p35 p45
          (candle_cv_fs_interval_neg p55)))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten (candle_cv_fs_interval_neg p00) p01 p02
          (candle_cv_fs_angle_interval_scale_neg_two p03) p04 p05
          (candle_cv_fs_interval_neg p12) p14 p25
          (candle_cv_fs_interval_neg p45)))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten p01 (candle_cv_fs_interval_neg p02) p03
          (candle_cv_fs_interval_neg p11) p12 p13
          (candle_cv_fs_angle_interval_scale_neg_two p14) p15 p25
          (candle_cv_fs_interval_neg p35)))
      (candle_cv_fs_angle_interval_sum
        (candle_cv_fs_angle_ten (candle_cv_fs_interval_neg p01) p02 p03
          p12 p14 (candle_cv_fs_interval_neg p22) p23 p24
          (candle_cv_fs_angle_interval_scale_neg_two p25)
          (candle_cv_fs_interval_neg p34)))`;;

let candle_cv_fs_angle_delta_hessian_def = new_definition
 `candle_cv_fs_angle_delta_hessian environment =
    let x0 = candle_cv_fs_interval_lookup (Cexp_num 0) environment in
    let x1 = candle_cv_fs_interval_lookup (Cexp_num 1) environment in
    let x2 = candle_cv_fs_interval_lookup (Cexp_num 2) environment in
    let x3 = candle_cv_fs_interval_lookup (Cexp_num 3) environment in
    let x4 = candle_cv_fs_interval_lookup (Cexp_num 4) environment in
    let x5 = candle_cv_fs_interval_lookup (Cexp_num 5) environment in
    let h00 = candle_cv_fs_angle_interval_scale_neg_two x3 in
    let h01 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x3 (Cexp_pair x4
        (Cexp_pair (candle_cv_fs_interval_neg x5) (Cexp_num 0)))) in
    let h02 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x3 (Cexp_pair (candle_cv_fs_interval_neg x4)
        (Cexp_pair x5 (Cexp_num 0)))) in
    let h03 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_interval_scale_neg_two x0) x1 x2
        (candle_cv_fs_angle_interval_scale_neg_two x3) x4 x5) in
    let h04 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x1 (Cexp_pair (candle_cv_fs_interval_neg x2)
        (Cexp_pair x3 (Cexp_num 0)))) in
    let h05 = candle_cv_fs_angle_interval_sum
      (Cexp_pair (candle_cv_fs_interval_neg x1)
        (Cexp_pair x2 (Cexp_pair x3 (Cexp_num 0)))) in
    let h11 = candle_cv_fs_angle_interval_scale_neg_two x4 in
    let h12 = candle_cv_fs_angle_interval_sum
      (Cexp_pair (candle_cv_fs_interval_neg x3)
        (Cexp_pair x4 (Cexp_pair x5 (Cexp_num 0)))) in
    let h13 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x0 (Cexp_pair (candle_cv_fs_interval_neg x2)
        (Cexp_pair x4 (Cexp_num 0)))) in
    let h14 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0
        (candle_cv_fs_angle_interval_scale_neg_two x1) x2 x3
        (candle_cv_fs_angle_interval_scale_neg_two x4) x5) in
    let h15 = candle_cv_fs_angle_interval_sum
      (Cexp_pair (candle_cv_fs_interval_neg x0)
        (Cexp_pair x2 (Cexp_pair x4 (Cexp_num 0)))) in
    let h22 = candle_cv_fs_angle_interval_scale_neg_two x5 in
    let h23 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x0 (Cexp_pair (candle_cv_fs_interval_neg x1)
        (Cexp_pair x5 (Cexp_num 0)))) in
    let h24 = candle_cv_fs_angle_interval_sum
      (Cexp_pair (candle_cv_fs_interval_neg x0)
        (Cexp_pair x1 (Cexp_pair x5 (Cexp_num 0)))) in
    let h25 = candle_cv_fs_angle_interval_sum
      (candle_cv_fs_angle_six x0 x1
        (candle_cv_fs_angle_interval_scale_neg_two x2) x3 x4
        (candle_cv_fs_angle_interval_scale_neg_two x5)) in
    let h33 = candle_cv_fs_angle_interval_scale_neg_two x0 in
    let h34 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x0 (Cexp_pair x1
        (Cexp_pair (candle_cv_fs_interval_neg x5) (Cexp_num 0)))) in
    let h35 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x0 (Cexp_pair x2
        (Cexp_pair (candle_cv_fs_interval_neg x4) (Cexp_num 0)))) in
    let h44 = candle_cv_fs_angle_interval_scale_neg_two x1 in
    let h45 = candle_cv_fs_angle_interval_sum
      (Cexp_pair x1 (Cexp_pair x2
        (Cexp_pair (candle_cv_fs_interval_neg x3) (Cexp_num 0)))) in
    let h55 = candle_cv_fs_angle_interval_scale_neg_two x2 in
    candle_cv_fs_angle_six
      (candle_cv_fs_angle_six h00 h01 h02 h03 h04 h05)
      (candle_cv_fs_angle_six h01 h11 h12 h13 h14 h15)
      (candle_cv_fs_angle_six h02 h12 h22 h23 h24 h25)
      (candle_cv_fs_angle_six h03 h13 h23 h33 h34 h35)
      (candle_cv_fs_angle_six h04 h14 h24 h34 h44 h45)
      (candle_cv_fs_angle_six h05 h15 h25 h35 h45 h55)`;;

let candle_cv_fs_angle_matrix_lookup_def = new_definition
 `candle_cv_fs_angle_matrix_lookup rowindex colindex matrixvalue =
    candle_cv_fs_interval_lookup colindex
      (candle_cv_fs_interval_lookup rowindex matrixvalue)`;;

let candle_cv_fs_angle_q_gradient_entry_def = new_definition
 `candle_cv_fs_angle_q_gradient_entry
      coordinate x0 deltavalue delta_gradient =
    candle_cv_fs_angle_interval_scale (Cexp_num 4)
      (candle_cv_fs_interval_add
        (candle_cv_fs_angle_interval_mul x0
          (candle_cv_fs_interval_lookup coordinate delta_gradient))
        (Cexp_if (Cexp_eq coordinate (Cexp_num 0)) deltavalue
          candle_cv_fs_interval_zero))`;;

let candle_cv_fs_angle_q_hessian_entry_def = new_definition
 `candle_cv_fs_angle_q_hessian_entry
      rowindex colindex x0 delta_gradient delta_hessian =
    candle_cv_fs_angle_interval_scale (Cexp_num 4)
      (candle_cv_fs_interval_add
        (candle_cv_fs_interval_add
          (candle_cv_fs_angle_interval_mul x0
            (candle_cv_fs_angle_matrix_lookup
              rowindex colindex delta_hessian))
          (Cexp_if (Cexp_eq rowindex (Cexp_num 0))
            (candle_cv_fs_interval_lookup colindex delta_gradient)
            candle_cv_fs_interval_zero))
        (Cexp_if (Cexp_eq colindex (Cexp_num 0))
          (candle_cv_fs_interval_lookup rowindex delta_gradient)
          candle_cv_fs_interval_zero))`;;

let candle_cv_fs_angle_q_hessian_def = new_definition
 `candle_cv_fs_angle_q_hessian x0 delta_gradient delta_hessian =
    candle_cv_fs_angle_six
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 0) (Cexp_num 5) x0 delta_gradient delta_hessian))
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 1) (Cexp_num 5) x0 delta_gradient delta_hessian))
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 2) (Cexp_num 5) x0 delta_gradient delta_hessian))
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 3) (Cexp_num 5) x0 delta_gradient delta_hessian))
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 4) (Cexp_num 5) x0 delta_gradient delta_hessian))
      (candle_cv_fs_angle_six
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 0) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 1) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 2) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 3) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 4) x0 delta_gradient delta_hessian)
        (candle_cv_fs_angle_q_hessian_entry (Cexp_num 5) (Cexp_num 5) x0 delta_gradient delta_hessian))`;;

let candle_cv_fs_angle_four_x0_delta_def = new_definition
 `candle_cv_fs_angle_four_x0_delta center_environment box_environment radii =
    let center_x0 = candle_cv_fs_interval_lookup (Cexp_num 0) center_environment in
    let box_x0 = candle_cv_fs_interval_lookup (Cexp_num 0) box_environment in
    let center_delta = candle_cv_fs_angle_delta_value center_environment in
    let center_delta_gradient =
      candle_cv_fs_angle_delta_gradient center_environment in
    let box_delta_hessian =
      candle_cv_fs_angle_delta_hessian box_environment in
    let box_delta_gradient =
      candle_cv_fs_gradient_bounds radii center_delta_gradient
        box_delta_hessian in
    let center_gradient = candle_cv_fs_angle_six
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 0) center_x0 center_delta center_delta_gradient)
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 1) center_x0 center_delta center_delta_gradient)
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 2) center_x0 center_delta center_delta_gradient)
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 3) center_x0 center_delta center_delta_gradient)
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 4) center_x0 center_delta center_delta_gradient)
      (candle_cv_fs_angle_q_gradient_entry (Cexp_num 5) center_x0 center_delta center_delta_gradient) in
    let box_hessian =
      candle_cv_fs_angle_q_hessian box_x0 box_delta_gradient
        box_delta_hessian in
    candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      (candle_cv_fs_first_make
        (candle_cv_fs_angle_interval_scale (Cexp_num 4)
          (candle_cv_fs_angle_interval_mul center_x0 center_delta))
        center_gradient)
      box_hessian`;;

let candle_cv_fs_angle_four_x0_delta_q_def = new_definition
 `candle_cv_fs_angle_four_x0_delta_q center_boxes boxes radii =
    candle_cv_fs_angle_four_x0_delta
      (candle_cv_fs_interval_list_of_q center_boxes)
      (candle_cv_fs_interval_list_of_q boxes)
      (candle_cv_fs_list_of_q radii)`;;

let candle_cv_fs_angle_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fixed_nonlinear_compute_eqs
      (map SPEC_ALL
        [candle_cv_fs_angle_six_def;
         candle_cv_fs_angle_seven_def;
         candle_cv_fs_angle_ten_def;
         candle_cv_fs_angle_interval_sum_compute;
         candle_cv_fs_angle_interval_scale_def;
         candle_cv_fs_angle_interval_scale_neg_two_def;
         candle_cv_fs_angle_interval_mul_def;
         candle_cv_fs_angle_delta_value_def;
         candle_cv_fs_angle_delta_gradient_def;
         candle_cv_fs_angle_delta_hessian_def;
         candle_cv_fs_angle_matrix_lookup_def;
         candle_cv_fs_angle_q_gradient_entry_def;
         candle_cv_fs_angle_q_hessian_entry_def;
         candle_cv_fs_angle_q_hessian_def;
         candle_cv_fs_angle_four_x0_delta_def;
         candle_cv_fs_angle_four_x0_delta_q_def]));;

end;;
