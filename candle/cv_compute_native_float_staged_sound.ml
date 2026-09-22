(* ========================================================================== *)
(* One-shot soundness for staged nonnegative native-float polynomials.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. The source value keeps every input factor       *)
(* symbolic. The final theorem consumes one validity fact for the complete    *)
(* staged program and relates that source directly to the computed result.     *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_staged_validity.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_mul;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;
open Candle_cv_native_float_staged_polynomial;;
open Candle_cv_native_float_staged_validity;;

let candle_nf_staged_product_scaled_value_def = define
 `(candle_nf_staged_product_scaled_value radix scale
      ([]:(num list#(num#num))list) = &1) /\
  (candle_nf_staged_product_scaled_value radix scale (CONS h t) =
     (&(candle_nf_value radix (SND h)) / &(radix EXP scale)) *
     candle_nf_staged_product_scaled_value radix scale t)`;;

let candle_nf_staged_polynomial_scaled_value_def = define
 `(candle_nf_staged_polynomial_scaled_value radix scale
      ([]:(((num list#(num#num))list)#(num list#num list))list) = &0) /\
  (candle_nf_staged_polynomial_scaled_value radix scale (CONS h t) =
     candle_nf_staged_product_scaled_value radix scale (FST h) +
     candle_nf_staged_polynomial_scaled_value radix scale t)`;;

let candle_nf_staged_product_scaled_quotient = prove
 (`!steps radix scale.
     ~(radix = 0)
     ==> candle_nf_staged_product_scaled_value radix scale steps =
         &(candle_nf_staged_product_value radix steps) /
         &(radix EXP scale) pow LENGTH steps`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_REWRITE_TAC
      [candle_nf_staged_product_scaled_value_def;
       candle_nf_staged_product_value_def; LENGTH; real_pow;
       REAL_OF_NUM_MUL; REAL_DIV_1];
    FIRST_X_ASSUM (LABEL_TAC "IH") THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "IH" (fun ih ->
      ASSUME_TAC
        (MATCH_MP
          (SPECL [`radix:num`;`scale:num`] ih)
          (ASSUME `~(radix = 0)`))) THEN
    ASM_REWRITE_TAC
      [candle_nf_staged_product_scaled_value_def;
       candle_nf_staged_product_value_def; LENGTH; real_pow;
       REAL_OF_NUM_MUL] THEN
    REWRITE_TAC
      [real_div; REAL_INV_MUL; REAL_OF_NUM_MUL; REAL_MUL_AC;
       MULT_SYM]]);;

let candle_nf_staged_product_scaled_bound = prove
 (`!steps radix scale limit.
     ~(radix = 0) /\
     candle_nf_staged_product_valid radix scale limit steps (1,scale)
     ==> candle_nf_staged_product_scaled_value radix scale steps <=
         &(candle_nf_value radix
             (candle_nf_staged_product radix scale limit steps (1,scale))) /
         &(radix EXP scale)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[candle_nf_staged_product_scaled_quotient] THEN
  SUBGOAL_THEN `&0 < &(radix EXP scale)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; EXP_LT_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(p / q) * d = (p * d) / q`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  REWRITE_TAC
    [REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  MP_TAC
    (SPECL
      [`steps:(num list#(num#num))list`; `radix:num`; `scale:num`;
       `limit:num`; `(1,scale):num#num`]
      candle_nf_staged_product_sound) THEN
  ASM_REWRITE_TAC
    [candle_nf_value_def; FST; SND; MULT_CLAUSES] THEN
  MESON_TAC[MULT_SYM]);;

let candle_nf_staged_polynomial_scaled_source_bound = prove
 (`!jobs radix scale limit acc.
     ~(radix = 0) /\
     candle_nf_staged_polynomial_valid radix scale limit jobs acc
     ==> candle_nf_staged_polynomial_scaled_value radix scale jobs <=
         &(candle_nf_staged_polynomial_value radix scale limit jobs) /
         &(radix EXP scale)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_scaled_value_def;
                candle_nf_staged_polynomial_value_def;
                candle_nf_staged_polynomial_valid_def;
                real_div; REAL_MUL_LZERO; REAL_LE_REFL];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_valid_def;
                candle_nf_staged_polynomial_scaled_value_def;
                candle_nf_staged_polynomial_value_def] THEN
    STRIP_TAC THEN
    REWRITE_TAC[real_div; GSYM REAL_OF_NUM_ADD; REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC
        (REWRITE_RULE[real_div]
          candle_nf_staged_product_scaled_bound) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[real_div]]]);;

let _ = ();;

let candle_nf_staged_polynomial_scaled_sound_goal =
 `!jobs radix scale limit acc.
     ~(radix = 0) /\
     candle_nf_staged_polynomial_valid radix scale limit jobs acc
     ==> &(candle_nf_value radix acc) / &(radix EXP scale) +
           candle_nf_staged_polynomial_scaled_value radix scale jobs <=
         &(candle_nf_value radix
             (candle_nf_staged_polynomial radix scale limit jobs acc)) /
         &(radix EXP scale)`;;

let candle_nf_staged_polynomial_scaled_sound_tactic =
  REPEAT STRIP_TAC THEN
  MP_TAC
    (MATCH_MP
      (SPECL
        [`jobs:(((num list#(num#num))list)#(num list#num list))list`;
         `radix:num`; `scale:num`; `limit:num`; `acc:num#num`]
        candle_nf_staged_polynomial_scaled_source_bound)
      (CONJ
        (ASSUME `~(radix = 0)`)
        (ASSUME
          `candle_nf_staged_polynomial_valid radix scale limit jobs acc`))) THEN
  DISCH_THEN (LABEL_TAC "SOURCE") THEN
  MP_TAC
    (MATCH_MP
      (SPECL
        [`jobs:(((num list#(num#num))list)#(num list#num list))list`;
         `radix:num`; `scale:num`; `limit:num`; `acc:num#num`]
        candle_nf_staged_polynomial_sound)
      (CONJ
        (ASSUME `~(radix = 0)`)
        (ASSUME
          `candle_nf_staged_polynomial_valid radix scale limit jobs acc`))) THEN
  DISCH_THEN (LABEL_TAC "POLYNOMIAL") THEN
  SUBGOAL_THEN `&0 <= inv(&(radix EXP scale))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_INV_EQ; REAL_OF_NUM_LE; LE_0];
    ALL_TAC] THEN
  USE_THEN "SOURCE" (fun source ->
    USE_THEN "POLYNOMIAL" (fun polynomial ->
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
        `&(candle_nf_value radix acc) / &(radix EXP scale) +
         &(candle_nf_staged_polynomial_value radix scale limit jobs) /
           &(radix EXP scale)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_ADD2 THEN
        ASM_REWRITE_TAC[REAL_LE_REFL];
        REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE]]));;

let candle_nf_staged_polynomial_scaled_sound_proof =
  (candle_nf_staged_polynomial_scaled_sound_goal,
   candle_nf_staged_polynomial_scaled_sound_tactic);;

let candle_nf_staged_polynomial_scaled_sound =
  prove candle_nf_staged_polynomial_scaled_sound_proof;;

let candle_cv_nf_boolean_true = prove
 (`!p. Cexp_num (if p then SUC 0 else 0) = Cexp_num 1 ==> p`,
  GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  REWRITE_TAC[injectivity "cval"] THEN ARITH_TAC);;
