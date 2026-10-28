(* ========================================================================== *)
(* Exact compact gradient of the Flyspeck delta polynomial.                   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This mirrors the signed pair-product table of *)
(* the optimized word checker, including duplicate terms and left-fold sum   *)
(* order.  The six components are kept as one operation so later specialized *)
(* Taylor states share one source-generic containment theorem.                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_packed_source_delta_hessian.ml";;

module Candle_cv_analytic_expr_packed_source_delta_gradient = struct

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_packed_source_delta_value;;
open Candle_cv_analytic_expr_packed_source_delta_hessian;;

let candle_q_packed_delta_gradient_six_def = new_definition
 `candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5 =
    let p00 = candle_q_interval_mul x0 x0 in
    let p01 = candle_q_interval_mul x0 x1 in
    let p02 = candle_q_interval_mul x0 x2 in
    let p03 = candle_q_interval_mul x0 x3 in
    let p04 = candle_q_interval_mul x0 x4 in
    let p05 = candle_q_interval_mul x0 x5 in
    let p11 = candle_q_interval_mul x1 x1 in
    let p12 = candle_q_interval_mul x1 x2 in
    let p13 = candle_q_interval_mul x1 x3 in
    let p14 = candle_q_interval_mul x1 x4 in
    let p15 = candle_q_interval_mul x1 x5 in
    let p22 = candle_q_interval_mul x2 x2 in
    let p23 = candle_q_interval_mul x2 x3 in
    let p24 = candle_q_interval_mul x2 x4 in
    let p25 = candle_q_interval_mul x2 x5 in
    let p33 = candle_q_interval_mul x3 x3 in
    let p34 = candle_q_interval_mul x3 x4 in
    let p35 = candle_q_interval_mul x3 x5 in
    let p44 = candle_q_interval_mul x4 x4 in
    let p45 = candle_q_interval_mul x4 x5 in
    let p55 = candle_q_interval_mul x5 x5 in
    [candle_q_packed_delta_sum
       [candle_q_interval_neg p03;candle_q_interval_neg p03;
        p13;p14;candle_q_interval_neg p15;p23;
        candle_q_interval_neg p24;p25;candle_q_interval_neg p33;p34;p35];
     candle_q_packed_delta_sum
       [p03;p04;candle_q_interval_neg p05;
        candle_q_interval_neg p14;candle_q_interval_neg p14;
        candle_q_interval_neg p23;p24;p25;p34;
        candle_q_interval_neg p44;p45];
     candle_q_packed_delta_sum
       [p03;candle_q_interval_neg p04;p05;
        candle_q_interval_neg p13;p14;p15;
        candle_q_interval_neg p25;candle_q_interval_neg p25;
        p35;p45;candle_q_interval_neg p55];
     candle_q_packed_delta_sum
       [candle_q_interval_neg p00;p01;p02;
        candle_q_interval_neg p03;candle_q_interval_neg p03;
        p04;p05;candle_q_interval_neg p12;p14;p25;
        candle_q_interval_neg p45];
     candle_q_packed_delta_sum
       [p01;candle_q_interval_neg p02;p03;
        candle_q_interval_neg p11;p12;p13;
        candle_q_interval_neg p14;candle_q_interval_neg p14;
        p15;p25;candle_q_interval_neg p35];
     candle_q_packed_delta_sum
       [candle_q_interval_neg p01;p02;p03;p12;p14;
        candle_q_interval_neg p22;p23;p24;
        candle_q_interval_neg p25;candle_q_interval_neg p25;
        candle_q_interval_neg p34]]`;;

let candle_real_packed_delta_gradient_six_def = new_definition
 `candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5 =
    let p00 = v0 * v0 in
    let p01 = v0 * v1 in
    let p02 = v0 * v2 in
    let p03 = v0 * v3 in
    let p04 = v0 * v4 in
    let p05 = v0 * v5 in
    let p11 = v1 * v1 in
    let p12 = v1 * v2 in
    let p13 = v1 * v3 in
    let p14 = v1 * v4 in
    let p15 = v1 * v5 in
    let p22 = v2 * v2 in
    let p23 = v2 * v3 in
    let p24 = v2 * v4 in
    let p25 = v2 * v5 in
    let p33 = v3 * v3 in
    let p34 = v3 * v4 in
    let p35 = v3 * v5 in
    let p44 = v4 * v4 in
    let p45 = v4 * v5 in
    let p55 = v5 * v5 in
    [candle_real_packed_delta_sum
       [--p03;--p03;p13;p14;--p15;p23;--p24;p25;--p33;p34;p35];
     candle_real_packed_delta_sum
       [p03;p04;--p05;--p14;--p14;--p23;p24;p25;p34;--p44;p45];
     candle_real_packed_delta_sum
       [p03;--p04;p05;--p13;p14;p15;--p25;--p25;p35;p45;--p55];
     candle_real_packed_delta_sum
       [--p00;p01;p02;--p03;--p03;p04;p05;--p12;p14;p25;--p45];
     candle_real_packed_delta_sum
       [p01;--p02;p03;--p11;p12;p13;--p14;--p14;p15;p25;--p35];
     candle_real_packed_delta_sum
       [--p01;p02;p03;p12;p14;--p22;p23;p24;--p25;--p25;--p34]]`;;

let candle_q_packed_delta_gradient_six_sound = prove
 (`!x0 x1 x2 x3 x4 x5 v0 v1 v2 v3 v4 v5.
     candle_q_interval_contains x0 v0 /\
     candle_q_interval_contains x1 v1 /\
     candle_q_interval_contains x2 v2 /\
     candle_q_interval_contains x3 v3 /\
     candle_q_interval_contains x4 v4 /\
     candle_q_interval_contains x5 v5
     ==>
     ALL2 candle_q_interval_contains
       (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)
       (candle_real_packed_delta_gradient_six v0 v1 v2 v3 v4 v5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_packed_delta_gradient_six_def;
              candle_real_packed_delta_gradient_six_def;
              LET_DEF; LET_END_DEF; ALL2] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC candle_q_packed_delta_sum_sound THEN
  REWRITE_TAC[ALL2] THEN
  ASM_SIMP_TAC[candle_q_interval_mul_sound;
               candle_q_interval_neg_sound]);;

let candle_cv_q_packed_delta_eleven_def = new_definition
 `candle_cv_q_packed_delta_eleven
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =
    Cexp_pair a0 (Cexp_pair a1 (Cexp_pair a2 (Cexp_pair a3
      (Cexp_pair a4 (Cexp_pair a5 (Cexp_pair a6 (Cexp_pair a7
        (Cexp_pair a8 (Cexp_pair a9 (Cexp_pair a10
          (Cexp_num 0)))))))))))`;;

let candle_cv_q_packed_delta_eleven_correct = prove
 (`!a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10.
     candle_cv_q_packed_delta_eleven
       (candle_cv_q_interval a0) (candle_cv_q_interval a1)
       (candle_cv_q_interval a2) (candle_cv_q_interval a3)
       (candle_cv_q_interval a4) (candle_cv_q_interval a5)
       (candle_cv_q_interval a6) (candle_cv_q_interval a7)
       (candle_cv_q_interval a8) (candle_cv_q_interval a9)
       (candle_cv_q_interval a10) =
     candle_cv_q_interval_list
       [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10]`,
  REWRITE_TAC[candle_cv_q_packed_delta_eleven_def;
              candle_cv_q_interval_list_def]);;

let candle_cv_q_packed_delta_gradient_six_def = new_definition
 `candle_cv_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5 =
    let p00 = candle_cv_q_interval_mul x0 x0 in
    let p01 = candle_cv_q_interval_mul x0 x1 in
    let p02 = candle_cv_q_interval_mul x0 x2 in
    let p03 = candle_cv_q_interval_mul x0 x3 in
    let p04 = candle_cv_q_interval_mul x0 x4 in
    let p05 = candle_cv_q_interval_mul x0 x5 in
    let p11 = candle_cv_q_interval_mul x1 x1 in
    let p12 = candle_cv_q_interval_mul x1 x2 in
    let p13 = candle_cv_q_interval_mul x1 x3 in
    let p14 = candle_cv_q_interval_mul x1 x4 in
    let p15 = candle_cv_q_interval_mul x1 x5 in
    let p22 = candle_cv_q_interval_mul x2 x2 in
    let p23 = candle_cv_q_interval_mul x2 x3 in
    let p24 = candle_cv_q_interval_mul x2 x4 in
    let p25 = candle_cv_q_interval_mul x2 x5 in
    let p33 = candle_cv_q_interval_mul x3 x3 in
    let p34 = candle_cv_q_interval_mul x3 x4 in
    let p35 = candle_cv_q_interval_mul x3 x5 in
    let p44 = candle_cv_q_interval_mul x4 x4 in
    let p45 = candle_cv_q_interval_mul x4 x5 in
    let p55 = candle_cv_q_interval_mul x5 x5 in
    let g0 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        (candle_cv_q_interval_neg p03) (candle_cv_q_interval_neg p03)
        p13 p14 (candle_cv_q_interval_neg p15) p23
        (candle_cv_q_interval_neg p24) p25
        (candle_cv_q_interval_neg p33) p34 p35) in
    let g1 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        p03 p04 (candle_cv_q_interval_neg p05)
        (candle_cv_q_interval_neg p14) (candle_cv_q_interval_neg p14)
        (candle_cv_q_interval_neg p23) p24 p25 p34
        (candle_cv_q_interval_neg p44) p45) in
    let g2 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        p03 (candle_cv_q_interval_neg p04) p05
        (candle_cv_q_interval_neg p13) p14 p15
        (candle_cv_q_interval_neg p25) (candle_cv_q_interval_neg p25)
        p35 p45 (candle_cv_q_interval_neg p55)) in
    let g3 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        (candle_cv_q_interval_neg p00) p01 p02
        (candle_cv_q_interval_neg p03) (candle_cv_q_interval_neg p03)
        p04 p05 (candle_cv_q_interval_neg p12) p14 p25
        (candle_cv_q_interval_neg p45)) in
    let g4 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        p01 (candle_cv_q_interval_neg p02) p03
        (candle_cv_q_interval_neg p11) p12 p13
        (candle_cv_q_interval_neg p14) (candle_cv_q_interval_neg p14)
        p15 p25 (candle_cv_q_interval_neg p35)) in
    let g5 = candle_cv_q_packed_delta_sum
      (candle_cv_q_packed_delta_eleven
        (candle_cv_q_interval_neg p01) p02 p03 p12 p14
        (candle_cv_q_interval_neg p22) p23 p24
        (candle_cv_q_interval_neg p25) (candle_cv_q_interval_neg p25)
        (candle_cv_q_interval_neg p34)) in
    candle_cv_q_packed_delta_six g0 g1 g2 g3 g4 g5`;;

let candle_cv_q_packed_delta_gradient_six_correct = prove
 (`!x0 x1 x2 x3 x4 x5.
     candle_cv_q_packed_delta_gradient_six
       (candle_cv_q_interval x0) (candle_cv_q_interval x1)
       (candle_cv_q_interval x2) (candle_cv_q_interval x3)
       (candle_cv_q_interval x4) (candle_cv_q_interval x5) =
     candle_cv_q_interval_list
       (candle_q_packed_delta_gradient_six x0 x1 x2 x3 x4 x5)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_packed_delta_gradient_six_def;
              candle_q_packed_delta_gradient_six_def;
              candle_cv_q_interval_mul_correct;
              candle_cv_q_interval_neg_correct;
              candle_cv_q_packed_delta_eleven_correct;
              candle_cv_q_packed_delta_sum_correct;
              candle_cv_q_packed_delta_six_correct;
              LET_DEF; LET_END_DEF]);;

let candle_cv_q_packed_source_delta_gradient_compute_eqs =
  candle_cv_q_packed_source_delta_hessian_compute_eqs @
  map SPEC_ALL
    [candle_cv_q_packed_delta_eleven_def;
     candle_cv_q_packed_delta_gradient_six_def];;

if exists (fun theorem -> hyp theorem <> [])
    [candle_q_packed_delta_gradient_six_sound;
     candle_cv_q_packed_delta_eleven_correct;
     candle_cv_q_packed_delta_gradient_six_correct] then
  failwith "packed source delta gradient: assumptions";;

print_endline
  "CANDLE_CV_PACKED_SOURCE_DELTA_GRADIENT_OK DEVELOPMENT_NON_RELEASE";;

end;;
