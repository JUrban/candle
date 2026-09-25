(* ========================================================================== *)
(* Extended checked reduction for large reflected exact rationals.           *)
(*                                                                            *)
(* The base normalizer uses two 128-step Euclidean chunks.  Authentic         *)
(* action-296 Taylor rows need 500--645 steps before they can be accumulated. *)
(* This variant uses eight chunks (1024 steps) while retaining the same       *)
(* fail-closed divisor validation and exact representation theorem.           *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_normalize.ml";;

module Candle_cv_exact_rational_normalize_extended = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_linear_combination_normalize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_normalize;;

(* One initial 128-step chunk followed by seven guarded resumptions. *)
let candle_num_gcd_extended_def = new_definition
 `candle_num_gcd_extended a b =
    candle_num_gcd_state_finish
      (candle_num_gcd_state_resume
        (candle_num_gcd_state_resume
          (candle_num_gcd_state_resume
            (candle_num_gcd_state_resume
              (candle_num_gcd_state_resume
                (candle_num_gcd_state_resume
                  (candle_num_gcd_state_resume
                    (candle_num_gcd_state_chunk a b))))))))`;;

let candle_q_normalize_signed_extended_def = new_definition
 `candle_q_normalize_signed_extended (z:num#num) denominator =
    candle_q_normalize_verified z denominator
      (candle_num_gcd_extended (FST z + SND z) denominator)`;;

let candle_q_normalize_extended_def = new_definition
 `candle_q_normalize_extended (q:(num#num)#num) =
    candle_q_normalize_signed_extended
      (candle_lc_znormalize (FST q)) (candle_q_den q)`;;

let candle_q_add_normalized_extended_def = new_definition
 `candle_q_add_normalized_extended x y =
    candle_q_normalize_extended (candle_q_add x y)`;;

let candle_q_mul_normalized_extended_def = new_definition
 `candle_q_mul_normalized_extended x y =
    candle_q_normalize_extended (candle_q_mul x y)`;;

let candle_q_real_normalize_signed_extended = prove
 (`!z denominator.
     ~(denominator = 0)
     ==> candle_q_real
           (candle_q_normalize_signed_extended z denominator) =
         candle_lc_zreal z / &denominator`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_normalize_signed_extended_def] THEN
  MATCH_MP_TAC candle_q_real_normalize_verified THEN
  ASM_REWRITE_TAC[]);;

let candle_q_real_normalize_extended = prove
 (`!q. candle_q_real (candle_q_normalize_extended q) = candle_q_real q`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_normalize_extended_def] THEN
  SIMP_TAC[candle_q_real_normalize_signed_extended; NOT_SUC;
           candle_q_real_def; candle_q_den_def; FST; SND;
           candle_lc_zreal_normalize]);;

let candle_q_real_add_normalized_extended = prove
 (`!x y.
     candle_q_real (candle_q_add_normalized_extended x y) =
     candle_q_real x + candle_q_real y`,
  REWRITE_TAC[candle_q_add_normalized_extended_def;
              candle_q_real_normalize_extended; candle_q_real_add]);;

let candle_q_real_mul_normalized_extended = prove
 (`!x y.
     candle_q_real (candle_q_mul_normalized_extended x y) =
     candle_q_real x * candle_q_real y`,
  REWRITE_TAC[candle_q_mul_normalized_extended_def;
              candle_q_real_normalize_extended; candle_q_real_mul]);;

let candle_cv_num_gcd_extended_def = new_definition
 `candle_cv_num_gcd_extended a b =
    candle_cv_num_gcd_state_finish
      (candle_cv_num_gcd_state_resume
        (candle_cv_num_gcd_state_resume
          (candle_cv_num_gcd_state_resume
            (candle_cv_num_gcd_state_resume
              (candle_cv_num_gcd_state_resume
                (candle_cv_num_gcd_state_resume
                  (candle_cv_num_gcd_state_resume
                    (candle_cv_num_gcd_state_chunk a b))))))))`;;

let candle_cv_q_normalize_signed_extended_def = new_definition
 `candle_cv_q_normalize_signed_extended z denominator =
    candle_cv_q_normalize_verified z denominator
      (candle_cv_num_gcd_extended
        (Cexp_add (Cexp_fst z) (Cexp_snd z)) denominator)`;;

let candle_cv_q_normalize_extended_def = new_definition
 `candle_cv_q_normalize_extended q =
    candle_cv_q_normalize_signed_extended
      (candle_cv_lc_znormalize (Cexp_fst q))
      (candle_cv_q_den q)`;;

let candle_cv_q_add_normalized_extended_def = new_definition
 `candle_cv_q_add_normalized_extended x y =
    candle_cv_q_normalize_extended (candle_cv_q_add x y)`;;

let candle_cv_q_mul_normalized_extended_def = new_definition
 `candle_cv_q_mul_normalized_extended x y =
    candle_cv_q_normalize_extended (candle_cv_q_mul x y)`;;

let candle_cv_q_extended_normalized_compute_eqs =
  map SPEC_ALL
   [candle_cv_num_gcd_extended_def;
    candle_cv_q_normalize_signed_extended_def;
    candle_cv_q_normalize_extended_def;
    candle_cv_q_add_normalized_extended_def;
    candle_cv_q_mul_normalized_extended_def];;

let candle_cv_num_gcd_extended_correct = prove
 (`!a b.
     candle_cv_num_gcd_extended (Cexp_num a) (Cexp_num b) =
     Cexp_num (candle_num_gcd_extended a b)`,
  REWRITE_TAC[candle_cv_num_gcd_extended_def;
              candle_num_gcd_extended_def;
              candle_cv_num_gcd_state_chunk_correct;
              candle_cv_num_gcd_state_resume_correct;
              candle_cv_num_gcd_state_finish_correct]);;

let candle_cv_num_gcd_signed_extended_correct = prove
 (`!z denominator.
     candle_cv_num_gcd_extended
       (Cexp_add
         (Cexp_fst (candle_cv_lc_z z))
         (Cexp_snd (candle_cv_lc_z z)))
       (Cexp_num denominator) =
     Cexp_num
       (candle_num_gcd_extended (FST z + SND z) denominator)`,
  REWRITE_TAC[candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; candle_cv_num_gcd_extended_correct]);;

let candle_cv_q_normalize_signed_extended_correct = prove
 (`!z denominator.
     candle_cv_q_normalize_signed_extended
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_q (candle_q_normalize_signed_extended z denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_signed_extended_def;
              candle_q_normalize_signed_extended_def;
              candle_cv_num_gcd_signed_extended_correct;
              candle_cv_q_normalize_verified_correct]);;

let candle_cv_q_normalize_extended_correct = prove
 (`!q.
     candle_cv_q_normalize_extended (candle_cv_q q) =
     candle_cv_q (candle_q_normalize_extended q)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_extended_def;
              candle_q_normalize_extended_def;
              candle_cv_q_def; cexp_fst_def;
              candle_cv_lc_znormalize_correct;
              candle_cv_q_den_correct;
              candle_cv_q_normalize_signed_extended_correct]);;

let candle_cv_q_add_normalized_extended_correct = prove
 (`!x y.
     candle_cv_q_add_normalized_extended (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_add_normalized_extended x y)`,
  REWRITE_TAC[candle_cv_q_add_normalized_extended_def;
              candle_q_add_normalized_extended_def;
              candle_cv_q_add_correct;
              candle_cv_q_normalize_extended_correct]);;

let candle_cv_q_mul_normalized_extended_correct = prove
 (`!x y.
     candle_cv_q_mul_normalized_extended (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_mul_normalized_extended x y)`,
  REWRITE_TAC[candle_cv_q_mul_normalized_extended_def;
              candle_q_mul_normalized_extended_def;
              candle_cv_q_mul_correct;
              candle_cv_q_normalize_extended_correct]);;

end;;
