(* ========================================================================== *)
(* Proof-producing canonicalization of exact signed-pair accumulators.       *)
(*                                                                            *)
(* The fold deliberately represents an integer as an unreduced pair (p,n).   *)
(* This layer uses Kernel.compute to cancel the common natural part and      *)
(* proves that the resulting canonical pair has the same real denotation.    *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination.ml";;
needs "candle/cv_compute_linear_combination_realize.ml";;

module Candle_cv_linear_combination_normalize = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination;;
open Candle_cv_linear_combination_realize;;

let candle_lc_znormalize_def = new_definition
 `candle_lc_znormalize (z:num#num) =
    if FST z < SND z then (0,SND z - FST z)
    else (FST z - SND z,0)`;;

let candle_lc_vec_normalize_def = define
 `(candle_lc_vec_normalize ([]:(num#num)list) = []) /\
  (candle_lc_vec_normalize (CONS z zs) =
     CONS (candle_lc_znormalize z) (candle_lc_vec_normalize zs))`;;

let candle_lc_acc_normalize_def = new_definition
 `candle_lc_acc_normalize
    (acc:(num#num)list#(num#num)) =
    (candle_lc_vec_normalize (FST acc),candle_lc_znormalize (SND acc))`;;

let candle_cv_lc_znormalize_def = new_definition
 `candle_cv_lc_znormalize z =
    Cexp_if (Cexp_less (Cexp_fst z) (Cexp_snd z))
      (Cexp_pair (Cexp_num 0) (Cexp_sub (Cexp_snd z) (Cexp_fst z)))
      (Cexp_pair (Cexp_sub (Cexp_fst z) (Cexp_snd z)) (Cexp_num 0))`;;

let candle_cv_lc_vec_normalize_def = define
 `(candle_cv_lc_vec_normalize (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_lc_vec_normalize (Cexp_pair z zs) =
     Cexp_pair (candle_cv_lc_znormalize z)
               (candle_cv_lc_vec_normalize zs))`;;

let candle_cv_lc_acc_normalize_def = new_definition
 `candle_cv_lc_acc_normalize acc =
    Cexp_pair (candle_cv_lc_vec_normalize (Cexp_fst acc))
              (candle_cv_lc_znormalize (Cexp_snd acc))`;;

let candle_cv_lc_vec_normalize_compute = prove
 (`!xs. candle_cv_lc_vec_normalize xs =
     Cexp_if (Cexp_ispair xs)
       (Cexp_pair (candle_cv_lc_znormalize (Cexp_fst xs))
                  (candle_cv_lc_vec_normalize (Cexp_snd xs)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `xs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_lc_vec_normalize_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_lc_normalize_compute_eqs = map SPEC_ALL
 [candle_cv_lc_znormalize_def;
  candle_cv_lc_vec_normalize_compute;
  candle_cv_lc_acc_normalize_def];;

let candle_cv_lc_znormalize_correct = prove
 (`!z:num#num.
     candle_cv_lc_znormalize (candle_cv_lc_z z) =
     candle_cv_lc_z (candle_lc_znormalize z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_lc_znormalize_def; candle_cv_lc_z_def;
              candle_lc_znormalize_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def; cexp_sub_def] THEN
  COND_CASES_TAC THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_lc_vec_normalize_correct = prove
 (`!zs:(num#num)list.
     candle_cv_lc_vec_normalize (candle_cv_lc_vec zs) =
     candle_cv_lc_vec (candle_lc_vec_normalize zs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_lc_vec_def; candle_cv_lc_vec_normalize_def;
                  candle_lc_vec_normalize_def;
                  candle_cv_lc_znormalize_correct]);;

let candle_cv_lc_acc_normalize_correct = prove
 (`!acc:(num#num)list#(num#num).
     candle_cv_lc_acc_normalize (candle_cv_lc_acc acc) =
     candle_cv_lc_acc (candle_lc_acc_normalize acc)`,
  REWRITE_TAC[candle_cv_lc_acc_normalize_def; candle_cv_lc_acc_def;
              candle_lc_acc_normalize_def; cexp_fst_def; cexp_snd_def;
              candle_cv_lc_vec_normalize_correct;
              candle_cv_lc_znormalize_correct]);;

let candle_lc_zreal_normalize = prove
 (`!z:num#num.
     candle_lc_zreal (candle_lc_znormalize z) = candle_lc_zreal z`,
  REWRITE_TAC[FORALL_PAIR_THM; candle_lc_znormalize_def;
              candle_lc_zreal_def; FST; SND] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[REAL_SUB_LZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT];
    ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_OF_NUM_SUB_CASES] THEN
    ASM_REWRITE_TAC[GSYM NOT_LT]]);;

let candle_lc_vec_real_normalize = prove
 (`!variables coefficients.
     candle_lc_vec_real variables
       (candle_lc_vec_normalize coefficients) =
     candle_lc_vec_real variables coefficients`,
  LIST_INDUCT_TAC THENL
   [GEN_TAC THEN
    MP_TAC (ISPEC `coefficients:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_lc_vec_normalize_def; candle_lc_vec_real_def];
    GEN_TAC THEN
    MP_TAC (ISPEC `coefficients:(num#num)list` list_CASES) THEN
    DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_ALL_TAC
       (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    ASM_REWRITE_TAC[candle_lc_vec_normalize_def; candle_lc_vec_real_def;
                    candle_lc_zreal_normalize]]);;

let candle_lc_acc_real_normalize = prove
 (`!variables acc.
     candle_lc_acc_real variables (candle_lc_acc_normalize acc) =
     candle_lc_acc_real variables acc`,
  REWRITE_TAC[candle_lc_acc_real_def; candle_lc_acc_normalize_def;
              candle_lc_vec_real_normalize; candle_lc_zreal_normalize]);;

let candle_lc_inequality_normalize = prove
 (`!variables acc.
     (candle_lc_vec_real variables
        (FST (candle_lc_acc_normalize acc)) <=
      candle_lc_zreal (SND (candle_lc_acc_normalize acc)) <=>
      candle_lc_vec_real variables (FST acc) <=
      candle_lc_zreal (SND acc))`,
  REWRITE_TAC[candle_lc_acc_normalize_def; FST; SND;
              candle_lc_vec_real_normalize; candle_lc_zreal_normalize]);;

let candle_cv_lc_acc_normalize_conv acc_tm =
  let acc_rep_th =
    candle_cv_lc_acc_encode_conv
      (mk_comb (`candle_cv_lc_acc`,acc_tm)) in
  let acc_cv_tm = rand (concl acc_rep_th) in
  let compute_tm = mk_comb (`candle_cv_lc_acc_normalize`,acc_cv_tm) in
  let compute_th =
    compute candle_cv_lc_normalize_compute_eqs compute_tm in
  let correctness_th = SPEC acc_tm candle_cv_lc_acc_normalize_correct in
  let input_bridge_th =
    AP_TERM `candle_cv_lc_acc_normalize` acc_rep_th in
  let encoded_result_th =
    TRANS (SYM correctness_th) (TRANS input_bridge_th compute_th) in
  let decoded_result_th =
    AP_TERM `candle_cv_lc_acc_decode` encoded_result_th in
  REWRITE_RULE[candle_cv_lc_acc_roundtrip;
               candle_cv_lc_acc_decode_def;
               candle_cv_lc_vec_decode_def;
               candle_cv_lc_z_decode_def;
               candle_cv_lc_num_decode_def] decoded_result_th;;

end;;
