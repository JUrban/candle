(* ========================================================================== *)
(* Staged reflected arithmetic for nonnegative scaled radix floats.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Unlike the coarse polynomial evaluator, this *)
(* layer rounds after each multiplication and addition.  It therefore keeps  *)
(* intermediate mantissas bounded while Kernel.compute evaluates the whole   *)
(* operation sequence.  Every result is related to the ordinary pair model   *)
(* by proved correctness and upward-bound theorems.                           *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_mul.ml";;

module Candle_cv_native_float_staged = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_mul;;

(* An exact unary power witness.  The translation layer supplies a list whose
   length is the exponent gap for this addition.  This deliberately uses the
   same simple list recursion already supported by Candle's rounder. *)
let candle_nf_power_fuel_def = define
 `(candle_nf_power_fuel radix ([]:num list) = 1) /\
  (candle_nf_power_fuel radix (CONS h t) =
     radix * candle_nf_power_fuel radix t)`;;

let candle_nf_power_fuel_complete = prove
 (`!fuel radix.
     candle_nf_power_fuel radix fuel = radix EXP LENGTH fuel`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; candle_nf_power_fuel_def; EXP]);;

let candle_cv_nf_power_fuel_def = define
 `(candle_cv_nf_power_fuel radix (Cexp_num z) = Cexp_num 1) /\
  (candle_cv_nf_power_fuel radix (Cexp_pair h t) =
     Cexp_mul radix (candle_cv_nf_power_fuel radix t))`;;

let candle_cv_nf_power_fuel_compute = prove
 (`!radix fuel.
     candle_cv_nf_power_fuel radix fuel =
     Cexp_if (Cexp_ispair fuel)
       (Cexp_mul radix (candle_cv_nf_power_fuel radix (Cexp_snd fuel)))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_power_fuel_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_nf_power_fuel_correct = prove
 (`!fuel radix.
     candle_cv_nf_power_fuel (Cexp_num radix) (candle_nf_fuel fuel) =
     Cexp_num (candle_nf_power_fuel radix fuel)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_fuel_def; candle_nf_power_fuel_def;
                  candle_cv_nf_power_fuel_def; cexp_mul_def]);;

(* Exact exponent alignment followed by an upward mantissa round. *)
let candle_nf_add_raw_def = new_definition
 `candle_nf_add_raw radix power_fuel (x:num#num) y =
    if SND x < SND y then
      (FST x + FST y *
         candle_nf_power_fuel radix power_fuel,
       SND x)
    else
      (FST x *
         candle_nf_power_fuel radix power_fuel + FST y,
       SND y)`;;

let candle_nf_add_power_complete_def = new_definition
 `candle_nf_add_power_complete (power_fuel:num list)
      (x:num#num) (y:num#num) <=>
    LENGTH power_fuel =
      (if SND x < SND y then SND y - SND x else SND x - SND y)`;;

let candle_nf_add_raw_value = prove
 (`!radix power_fuel x y.
     candle_nf_add_power_complete power_fuel x y
     ==> candle_nf_value radix (candle_nf_add_raw radix power_fuel x y) =
         candle_nf_value radix x + candle_nf_value radix y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_nf_add_power_complete_def;
              candle_nf_add_raw_def; candle_nf_value_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND] THEN
  DISCH_TAC THEN
  ASM_REWRITE_TAC[candle_nf_power_fuel_complete] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM MULT_ASSOC; GSYM EXP_ADD] THENL
   [FIRST_ASSUM (fun th ->
      let le = MATCH_MP LT_IMP_LE th in
      ASM_REWRITE_TAC[MATCH_MP SUB_ADD le]);
    FIRST_ASSUM (fun th ->
      let not_lt_imp_le = fst (EQ_IMP_RULE (SPEC_ALL NOT_LT)) in
      let le = MATCH_MP not_lt_imp_le th in
      ASM_REWRITE_TAC[MATCH_MP SUB_ADD le])]);;

let candle_nf_add_round_hi_def = new_definition
 `candle_nf_add_round_hi radix limit round_fuel power_fuel
      (x:num#num) y =
    candle_nf_round_hi radix limit round_fuel
      (FST (candle_nf_add_raw radix power_fuel x y))
      (SND (candle_nf_add_raw radix power_fuel x y))`;;

let candle_nf_add_round_hi_sound = prove
 (`!radix limit round_fuel power_fuel x y.
     ~(radix = 0) /\ candle_nf_add_power_complete power_fuel x y
     ==> candle_nf_value radix x + candle_nf_value radix y <=
         candle_nf_value radix
           (candle_nf_add_round_hi
             radix limit round_fuel power_fuel x y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_add_round_hi_def] THEN
  FIRST_ASSUM (fun th ->
    REWRITE_TAC[GSYM (MATCH_MP candle_nf_add_raw_value th)]) THEN
  REWRITE_TAC[candle_nf_value_def] THEN
  MP_TAC
    (SPECL
      [`round_fuel:num list`; `radix:num`; `limit:num`;
       `FST (candle_nf_add_raw radix power_fuel
          (x:num#num) (y:num#num))`;
       `SND (candle_nf_add_raw radix power_fuel
          (x:num#num) (y:num#num))`]
      candle_nf_round_hi_sound) THEN
  ASM_REWRITE_TAC[]);;

let candle_cv_nf_add_raw_def = new_definition
 `candle_cv_nf_add_raw radix power_fuel x y =
    Cexp_if (Cexp_less (Cexp_snd x) (Cexp_snd y))
      (Cexp_pair
        (Cexp_add (Cexp_fst x)
          (Cexp_mul (Cexp_fst y)
            (candle_cv_nf_power_fuel radix power_fuel)))
        (Cexp_snd x))
      (Cexp_pair
        (Cexp_add
          (Cexp_mul (Cexp_fst x)
            (candle_cv_nf_power_fuel radix power_fuel))
          (Cexp_fst y))
        (Cexp_snd y))`;;

let candle_cv_nf_add_round_hi_def = new_definition
 `candle_cv_nf_add_round_hi radix limit round_fuel power_fuel x y =
    candle_cv_nf_round_hi radix limit round_fuel
      (Cexp_fst (candle_cv_nf_add_raw radix power_fuel x y))
      (Cexp_snd (candle_cv_nf_add_raw radix power_fuel x y))`;;

let candle_cv_nf_add_raw_correct = prove
 (`!radix power_fuel x y.
     candle_cv_nf_add_raw (Cexp_num radix) (candle_nf_fuel power_fuel)
       (candle_nf_pair x) (candle_nf_pair y) =
     candle_nf_pair (candle_nf_add_raw radix power_fuel x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_add_raw_def; candle_nf_add_raw_def;
              candle_nf_pair_def; cexp_fst_def; cexp_snd_def;
              cexp_less_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[cexp_if_def; candle_cv_nf_power_fuel_correct;
                  cexp_sub_def; cexp_mul_def; cexp_add_def]);;

let candle_cv_nf_add_round_hi_correct = prove
 (`!radix limit round_fuel power_fuel x y.
     candle_cv_nf_add_round_hi (Cexp_num radix) (Cexp_num limit)
       (candle_nf_fuel round_fuel) (candle_nf_fuel power_fuel)
       (candle_nf_pair x) (candle_nf_pair y) =
     candle_nf_pair
       (candle_nf_add_round_hi
         radix limit round_fuel power_fuel x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_add_round_hi_def;
              candle_nf_add_round_hi_def;
              candle_cv_nf_add_raw_correct; candle_nf_pair_def;
              cexp_fst_def; cexp_snd_def;
              candle_cv_nf_round_hi_correct]);;

(* Multiplication of floats sharing a radix^scale denominator. *)
let candle_nf_le_mult_right = prove
 (`!a b c:num. a <= b ==> a * c <= b * c`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]);;

let candle_nf_scaled_mul_round_hi_def = new_definition
 `candle_nf_scaled_mul_round_hi radix scale limit fuel (x:num#num) y =
    candle_nf_round_hi radix limit fuel
      (FST x * FST y) ((SND x + SND y) - scale)`;;

let candle_nf_scaled_mul_round_hi_sound = prove
 (`!radix scale limit fuel x y.
     ~(radix = 0) /\ scale <= SND x + SND y
     ==> candle_nf_value radix x * candle_nf_value radix y <=
         candle_nf_value radix
           (candle_nf_scaled_mul_round_hi radix scale limit fuel x y) *
         radix EXP scale`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_nf_value_def; candle_nf_scaled_mul_round_hi_def] THEN
  MP_TAC
    (SPECL
      [`fuel:num list`; `radix:num`; `limit:num`;
       `FST (x:num#num) * FST (y:num#num)`;
       `(SND (x:num#num) + SND (y:num#num)) - scale`]
      candle_nf_round_hi_sound) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "ROUND") THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `(FST (x:num#num) * FST (y:num#num) *
       radix EXP ((SND x + SND y) - scale)) * radix EXP scale` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    SUBGOAL_THEN
     `radix EXP ((SND (x:num#num) + SND (y:num#num)) - scale) *
        radix EXP scale =
      radix EXP SND x * radix EXP SND y`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN ASM_SIMP_TAC[SUB_ADD];
      REWRITE_TAC[GSYM MULT_ASSOC] THEN ASM_REWRITE_TAC[] THEN
      MATCH_ACCEPT_TAC
       (AC MULT_AC
         `a * b * c * d = a * c * b * d:num`)];
    USE_THEN "ROUND" MP_TAC THEN
    MESON_TAC[candle_nf_le_mult_right; MULT_AC]]);;

let candle_cv_nf_scaled_mul_round_hi_def = new_definition
 `candle_cv_nf_scaled_mul_round_hi radix scale limit fuel x y =
    candle_cv_nf_round_hi radix limit fuel
      (Cexp_mul (Cexp_fst x) (Cexp_fst y))
      (Cexp_sub (Cexp_add (Cexp_snd x) (Cexp_snd y)) scale)`;;

let candle_cv_nf_scaled_mul_round_hi_correct = prove
 (`!radix scale limit fuel x y.
     candle_cv_nf_scaled_mul_round_hi
       (Cexp_num radix) (Cexp_num scale) (Cexp_num limit)
       (candle_nf_fuel fuel) (candle_nf_pair x) (candle_nf_pair y) =
     candle_nf_pair
       (candle_nf_scaled_mul_round_hi radix scale limit fuel x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_scaled_mul_round_hi_def;
              candle_nf_scaled_mul_round_hi_def;
              candle_nf_pair_def; cexp_fst_def; cexp_snd_def;
              cexp_mul_def; cexp_add_def; cexp_sub_def;
              candle_cv_nf_round_hi_correct]);;

let candle_cv_nf_staged_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_power_fuel_compute;
    candle_cv_nf_add_raw_def;
    candle_cv_nf_add_round_hi_def;
    candle_cv_nf_scaled_mul_round_hi_def;
    candle_cv_nf_round_hi_compute];;

end;;
