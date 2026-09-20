(* ========================================================================== *)
(* Coarse reflected native-float multiplication and directed rounding.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Multiplication, exponent addition, and the      *)
(* complete rounding loop execute behind one Kernel.compute call.             *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_core.ml";;

module Candle_cv_native_float_mul = struct

open Candle_cv_native_float_core;;

let candle_nf_value_def = new_definition
 `candle_nf_value radix (x:num#num) = FST x * radix EXP SND x`;;

let candle_nf_mul_pair_def = new_definition
 `candle_nf_mul_pair (x:num#num) y =
    (FST x * FST y,SND x + SND y)`;;

let candle_nf_mul_pair_value = prove
 (`!radix x y.
     candle_nf_value radix (candle_nf_mul_pair x y) =
     candle_nf_value radix x * candle_nf_value radix y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_nf_value_def; candle_nf_mul_pair_def; FST; SND; EXP_ADD] THEN
  MESON_TAC[MULT_AC]);;

let candle_nf_mul_round_lo_def = new_definition
 `candle_nf_mul_round_lo radix limit fuel (x:num#num) y =
    candle_nf_round_lo radix limit fuel
      (FST x * FST y) (SND x + SND y)`;;

let candle_nf_mul_round_hi_def = new_definition
 `candle_nf_mul_round_hi radix limit fuel (x:num#num) y =
    candle_nf_round_hi radix limit fuel
      (FST x * FST y) (SND x + SND y)`;;

let candle_nf_mul_round_lo_sound = prove
 (`!fuel radix limit x y.
     candle_nf_value radix (candle_nf_mul_round_lo radix limit fuel x y) <=
     candle_nf_value radix x * candle_nf_value radix y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_nf_value_def; candle_nf_mul_round_lo_def] THEN
  MP_TAC
    (SPECL
      [`fuel:num list`; `radix:num`; `limit:num`;
       `FST (x:num#num) * FST (y:num#num)`;
       `SND (x:num#num) + SND (y:num#num)`]
      candle_nf_round_lo_sound) THEN
  REWRITE_TAC[EXP_ADD] THEN MESON_TAC[MULT_AC]);;

let candle_nf_mul_round_hi_sound = prove
 (`!fuel radix limit x y. ~(radix = 0)
     ==> candle_nf_value radix x * candle_nf_value radix y <=
         candle_nf_value radix
           (candle_nf_mul_round_hi radix limit fuel x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_nf_value_def; candle_nf_mul_round_hi_def] THEN
  MP_TAC
    (SPECL
      [`fuel:num list`; `radix:num`; `limit:num`;
       `FST (x:num#num) * FST (y:num#num)`;
       `SND (x:num#num) + SND (y:num#num)`]
      candle_nf_round_hi_sound) THEN
  ASM_REWRITE_TAC[EXP_ADD] THEN MESON_TAC[MULT_AC]);;

let candle_cv_nf_mul_round_lo_def = new_definition
 `candle_cv_nf_mul_round_lo radix limit fuel x y =
    candle_cv_nf_round_lo radix limit fuel
      (Cexp_mul (Cexp_fst x) (Cexp_fst y))
      (Cexp_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_nf_mul_round_hi_def = new_definition
 `candle_cv_nf_mul_round_hi radix limit fuel x y =
    candle_cv_nf_round_hi radix limit fuel
      (Cexp_mul (Cexp_fst x) (Cexp_fst y))
      (Cexp_add (Cexp_snd x) (Cexp_snd y))`;;

let candle_cv_nf_mul_round_lo_correct = prove
 (`!fuel radix limit x y.
     candle_cv_nf_mul_round_lo (Cexp_num radix) (Cexp_num limit)
       (candle_nf_fuel fuel) (candle_nf_pair x) (candle_nf_pair y) =
     candle_nf_pair (candle_nf_mul_round_lo radix limit fuel x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_mul_round_lo_def; candle_nf_pair_def;
              cexp_fst_def; cexp_snd_def; cexp_mul_def; cexp_add_def;
              candle_nf_mul_round_lo_def; candle_cv_nf_round_lo_correct]);;

let candle_cv_nf_mul_round_hi_correct = prove
 (`!fuel radix limit x y.
     candle_cv_nf_mul_round_hi (Cexp_num radix) (Cexp_num limit)
       (candle_nf_fuel fuel) (candle_nf_pair x) (candle_nf_pair y) =
     candle_nf_pair (candle_nf_mul_round_hi radix limit fuel x y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_nf_mul_round_hi_def; candle_nf_pair_def;
              cexp_fst_def; cexp_snd_def; cexp_mul_def; cexp_add_def;
              candle_nf_mul_round_hi_def; candle_cv_nf_round_hi_correct]);;

let candle_cv_nf_mul_round_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_mul_round_lo_def;
    candle_cv_nf_mul_round_hi_def;
    candle_cv_nf_round_lo_compute;
    candle_cv_nf_round_hi_compute];;

end;;
