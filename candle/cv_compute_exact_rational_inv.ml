(* ========================================================================== *)
(* Exact reciprocal for reflected rational analytic nodes.                   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The operation is total at the data level and  *)
(* returns zero on a zero numerator.  Its real-semantics theorem is guarded   *)
(* by the corresponding exact nonzero predicate.                              *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_core.ml";;

module Candle_cv_exact_rational_inv = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;

let candle_q_nonzero_def = new_definition
 `candle_q_nonzero (q:(num#num)#num) <=>
    ~(FST (FST q) = SND (FST q))`;;

let candle_q_inv_def = new_definition
 `candle_q_inv (q:(num#num)#num) =
    if FST (FST q) < SND (FST q) then
      ((0,candle_q_den q),SND (FST q) - FST (FST q) - 1)
    else if SND (FST q) < FST (FST q) then
      ((candle_q_den q,0),FST (FST q) - SND (FST q) - 1)
    else (((0,0),0):(num#num)#num)`;;

let candle_real_neg_div_neg = prove
 (`!d x:real. --d / x = d / --x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG]);;

let candle_q_inv_real_negative = prove
 (`!a b c. a < b
       ==> candle_q_real (candle_q_inv (((a,b),c):(num#num)#num)) =
           inv (candle_q_real ((a,b),c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_inv_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC (b - a - 1) = b - a` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&(b - a):real) = &b - &a` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_DIV] THEN
  SUBGOAL_THEN `(&a - &b:real) = --(&b - &a)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUB_LZERO; candle_real_neg_div_neg]);;

let candle_q_inv_real_positive = prove
 (`!a b c. b < a
       ==> candle_q_real (candle_q_inv (((a,b),c):(num#num)#num)) =
           inv (candle_q_real ((a,b),c))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((a:num) < (b:num))` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_ANTISYM]; ALL_TAC] THEN
  REWRITE_TAC[candle_q_inv_def; candle_q_real_def; candle_q_den_def;
              candle_lc_zreal_def; FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC (a - b - 1) = a - b` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&(a - b):real) = &a - &b` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_SUB; LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_DIV; REAL_SUB_RZERO]);;

let candle_q_inv_real_components = prove
 (`!a b c. candle_q_nonzero (((a,b),c):(num#num)#num)
       ==> candle_q_real (candle_q_inv ((a,b),c)) =
           inv (candle_q_real ((a,b),c))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_nonzero_def; FST; SND] THEN DISCH_TAC THEN
  ASM_MESON_TAC[candle_q_inv_real_negative;
                candle_q_inv_real_positive; LT_CASES]);;

let candle_q_inv_real = prove
 (`!q. candle_q_nonzero q
       ==> candle_q_real (candle_q_inv q) = inv (candle_q_real q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MATCH_ACCEPT_TAC candle_q_inv_real_components);;

let candle_cv_q_inv_def = new_definition
 `candle_cv_q_inv q =
    Cexp_if
      (Cexp_less (Cexp_fst (Cexp_fst q)) (Cexp_snd (Cexp_fst q)))
      (Cexp_pair
        (Cexp_pair (Cexp_num 0) (candle_cv_q_den q))
        (Cexp_sub
          (Cexp_sub (Cexp_snd (Cexp_fst q))
                    (Cexp_fst (Cexp_fst q)))
          (Cexp_num 1)))
      (Cexp_if
        (Cexp_less (Cexp_snd (Cexp_fst q)) (Cexp_fst (Cexp_fst q)))
        (Cexp_pair
          (Cexp_pair (candle_cv_q_den q) (Cexp_num 0))
          (Cexp_sub
            (Cexp_sub (Cexp_fst (Cexp_fst q))
                      (Cexp_snd (Cexp_fst q)))
            (Cexp_num 1)))
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0))
                   (Cexp_num 0)))`;;

let candle_cv_q_inv_compute_eqs =
  candle_cv_q_compute_eqs @ [SPEC_ALL candle_cv_q_inv_def];;

let candle_cv_q_inv_correct_components = prove
 (`!a b c.
     candle_cv_q_inv (candle_cv_q (((a,b),c):(num#num)#num)) =
     candle_cv_q (candle_q_inv ((a,b),c))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_inv_def; candle_q_inv_def;
              candle_cv_q_den_def; candle_q_den_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              candle_cv_q_den_correct; cexp_fst_def; cexp_snd_def;
              cexp_less_def; cexp_if_def; cexp_sub_def; cexp_add_def] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[FST; SND; cexp_if_def]));;

let candle_cv_q_inv_correct = prove
 (`!q. candle_cv_q_inv (candle_cv_q q) =
       candle_cv_q (candle_q_inv q)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MATCH_ACCEPT_TAC candle_cv_q_inv_correct_components);;

end;;
