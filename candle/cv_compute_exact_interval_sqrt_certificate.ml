(* ========================================================================== *)
(* Proof-producing certificates for square-root interval enclosures.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Square roots of rational endpoints need not   *)
(* be rational.  An untrusted preparer may therefore supply rational lower   *)
(* and upper bounds; this reflected predicate checks their squared endpoint   *)
(* obligations exactly before the soundness theorem can authorize them.      *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_program.ml";;
needs "candle/cv_compute_exact_interval_square_core.ml";;

module Candle_cv_exact_interval_sqrt_certificate = struct

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;

let candle_q_interval_sqrt_certificate_def = new_definition
 `candle_q_interval_sqrt_certificate
    (input:((num#num)#num)#((num#num)#num))
    (output:((num#num)#num)#((num#num)#num)) <=>
    candle_q_le candle_q_zero (FST input) /\
    candle_q_le (FST input) (SND input) /\
    candle_q_le candle_q_zero (FST output) /\
    candle_q_le (FST output) (SND output) /\
    candle_q_le
      (candle_q_mul (FST output) (FST output)) (FST input) /\
    candle_q_le
      (SND input) (candle_q_mul (SND output) (SND output))`;;

let candle_real_interval_sqrt_certificate = prove
 (`!ilo ihi slo shi x:real.
     &0 <= ilo /\ ilo <= ihi /\
     &0 <= slo /\ slo <= shi /\
     slo * slo <= ilo /\ ihi <= shi * shi /\
     ilo <= x /\ x <= ihi
     ==> slo <= sqrt x /\ sqrt x <= shi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LSQRT THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

let candle_q_interval_sqrt_certificate_sound = prove
 (`!input output x.
     candle_q_interval_sqrt_certificate input output /\
     candle_q_interval_contains input x
     ==> candle_q_interval_contains output (sqrt x)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_interval_sqrt_certificate_def;
              candle_q_interval_contains_def; candle_q_le_real;
              candle_q_real_mul; candle_q_zero_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MESON_TAC[candle_real_interval_sqrt_certificate]);;

let candle_cv_q_interval_sqrt_certificate_def = new_definition
 `candle_cv_q_interval_sqrt_certificate input output =
    Cexp_if
      (candle_cv_q_le
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))
        (Cexp_fst input))
      (Cexp_if
        (candle_cv_q_le (Cexp_fst input) (Cexp_snd input))
        (Cexp_if
          (candle_cv_q_le
            (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0))
            (Cexp_fst output))
          (Cexp_if
            (candle_cv_q_le (Cexp_fst output) (Cexp_snd output))
            (Cexp_if
              (candle_cv_q_le
                (candle_cv_q_mul
                  (Cexp_fst output) (Cexp_fst output))
                (Cexp_fst input))
              (Cexp_if
                (candle_cv_q_le
                  (Cexp_snd input)
                  (candle_cv_q_mul
                    (Cexp_snd output) (Cexp_snd output)))
                (Cexp_num 1) (Cexp_num 0))
              (Cexp_num 0))
            (Cexp_num 0))
          (Cexp_num 0))
        (Cexp_num 0))
      (Cexp_num 0)`;;

let candle_cv_q_interval_sqrt_certificate_compute_eqs =
  candle_cv_q_order_compute_eqs @
  map SPEC_ALL [candle_cv_q_interval_sqrt_certificate_def];;

let candle_cv_q_sqrt_zero_literal = prove
 (`Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0)) (Cexp_num 0) =
   candle_cv_q candle_q_zero`,
  REWRITE_TAC[candle_q_zero_def; candle_cv_q_def;
              Candle_cv_linear_combination_core.candle_cv_lc_z_def;
              FST; SND]);;

let candle_cv_q_interval_sqrt_certificate_correct = prove
 (`!input output.
     candle_cv_q_interval_sqrt_certificate
       (candle_cv_q_interval input) (candle_cv_q_interval output) =
     Cexp_num
       (if candle_q_interval_sqrt_certificate input output then 1 else 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_sqrt_certificate_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_sqrt_zero_literal;
              candle_q_interval_sqrt_certificate_def;
              candle_cv_q_le_correct; candle_cv_q_mul_correct] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]));;

end;;
