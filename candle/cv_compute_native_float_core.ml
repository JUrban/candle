(* ========================================================================== *)
(* Reflected native-float multiplication with directed mantissa rounding.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. The ordinary representation is                 *)
(* ((sign,mantissa),exponent), matching Flyspeck's bool * num * num values.   *)
(* Rounding consumes an explicit list fuel. Exhausted fuel returns the exact  *)
(* remaining mantissa, so it affects compression but never soundness.         *)
(* ========================================================================== *)

needs "candle/compute.ml";;

module Candle_cv_native_float_core = struct

let candle_nf_fuel_def = define
 `(candle_nf_fuel ([]:num list) = Cexp_num 0) /\
  (candle_nf_fuel (CONS h t) =
     Cexp_pair (Cexp_num h) (candle_nf_fuel t))`;;

let candle_nf_pair_def = new_definition
 `candle_nf_pair (x:num#num) = Cexp_pair (Cexp_num (FST x)) (Cexp_num (SND x))`;;

let candle_nf_decode_num_def = define
 `(candle_nf_decode_num (Cexp_num n) = n) /\
  (candle_nf_decode_num (Cexp_pair x y) = 0)`;;

let candle_nf_decode_pair_def = define
 `(candle_nf_decode_pair (Cexp_num n) = (0,0)) /\
  (candle_nf_decode_pair (Cexp_pair x y) =
     (candle_nf_decode_num x,candle_nf_decode_num y))`;;

let candle_nf_pair_roundtrip = prove
 (`!x:num#num. candle_nf_decode_pair (candle_nf_pair x) = x`,
  REWRITE_TAC[candle_nf_pair_def; candle_nf_decode_pair_def;
              candle_nf_decode_num_def; PAIR]);;

let candle_nf_round_lo_def = define
 `(candle_nf_round_lo radix limit ([]:num list) n e = (n,e)) /\
  (candle_nf_round_lo radix limit (CONS h t) n e =
     if n < limit then (n,e)
     else candle_nf_round_lo radix limit t (n DIV radix) (SUC e))`;;

let candle_nf_round_hi_def = define
 `(candle_nf_round_hi radix limit ([]:num list) n e = (n,e)) /\
  (candle_nf_round_hi radix limit (CONS h t) n e =
     if n < limit then (n,e)
     else candle_nf_round_hi radix limit t
            (n DIV radix + if n MOD radix = 0 then 0 else 1)
            (SUC e))`;;

let candle_nf_round_lo_step = prove
 (`!radix n e.
     (n DIV radix) * radix EXP (SUC e) <= n * radix EXP e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP] THEN
  MP_TAC(SPECL [`n:num`; `radix:num`] DIV_MUL_LE) THEN
  MESON_TAC[LE_MULT2; LE_REFL; MULT_AC]);;

let candle_nf_ceil_div_step = prove
 (`!radix n. ~(radix = 0)
       ==> n <=
           (n DIV radix + if n MOD radix = 0 then 0 else 1) * radix`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `radix:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
      [ASSUME `n = n DIV radix * radix + n MOD radix`] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL];
    GEN_REWRITE_TAC LAND_CONV
      [ASSUME `n = n DIV radix * radix + n MOD radix`] THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; LE_ADD_LCANCEL] THEN
    ASM_MESON_TAC[LT_IMP_LE]]);;

let candle_nf_round_hi_step = prove
 (`!radix n e. ~(radix = 0)
       ==> n * radix EXP e <=
           (n DIV radix + if n MOD radix = 0 then 0 else 1) *
           radix EXP (SUC e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXP] THEN
  MP_TAC(SPECL [`radix:num`; `n:num`] candle_nf_ceil_div_step) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[LE_MULT2; LE_REFL; MULT_AC]);;

let candle_nf_round_lo_sound = prove
 (`!fuel radix limit n e.
     FST (candle_nf_round_lo radix limit fuel n e) *
       radix EXP SND (candle_nf_round_lo radix limit fuel n e)
     <= n * radix EXP e`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_nf_round_lo_def; FST; SND; LE_REFL];
    REPEAT GEN_TAC THEN REWRITE_TAC[candle_nf_round_lo_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND; LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(n DIV radix) * radix EXP (SUC e)` THEN
    ASM_MESON_TAC[candle_nf_round_lo_step]]);;

let candle_nf_round_hi_sound = prove
 (`!fuel radix limit n e. ~(radix = 0)
       ==> n * radix EXP e <=
           FST (candle_nf_round_hi radix limit fuel n e) *
           radix EXP SND (candle_nf_round_hi radix limit fuel n e)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_nf_round_hi_def; FST; SND; LE_REFL];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[candle_nf_round_hi_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[FST; SND; LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC
      `(n DIV radix + if n MOD radix = 0 then 0 else 1) *
       radix EXP (SUC e)` THEN
    ASM_MESON_TAC[candle_nf_round_hi_step]]);;

let candle_cv_nf_round_lo_def = define
 `(candle_cv_nf_round_lo radix limit (Cexp_num z) n e =
     Cexp_pair n e) /\
  (candle_cv_nf_round_lo radix limit (Cexp_pair h t) n e =
     Cexp_if (Cexp_less n limit)
       (Cexp_pair n e)
       (candle_cv_nf_round_lo radix limit t
          (Cexp_div n radix) (Cexp_add e (Cexp_num 1))))`;;

let candle_cv_nf_round_hi_def = define
 `(candle_cv_nf_round_hi radix limit (Cexp_num z) n e =
     Cexp_pair n e) /\
  (candle_cv_nf_round_hi radix limit (Cexp_pair h t) n e =
     Cexp_if (Cexp_less n limit)
       (Cexp_pair n e)
       (candle_cv_nf_round_hi radix limit t
          (Cexp_add (Cexp_div n radix)
            (Cexp_if (Cexp_eq (Cexp_mod n radix) (Cexp_num 0))
              (Cexp_num 0) (Cexp_num 1)))
          (Cexp_add e (Cexp_num 1))))`;;

let candle_cv_nf_round_lo_compute = prove
 (`!radix limit fuel n e.
     candle_cv_nf_round_lo radix limit fuel n e =
     Cexp_if (Cexp_ispair fuel)
       (Cexp_if (Cexp_less n limit)
         (Cexp_pair n e)
         (candle_cv_nf_round_lo radix limit (Cexp_snd fuel)
           (Cexp_div n radix) (Cexp_add e (Cexp_num 1))))
       (Cexp_pair n e)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_round_lo_def; cexp_if_def;
              cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_round_hi_compute = prove
 (`!radix limit fuel n e.
     candle_cv_nf_round_hi radix limit fuel n e =
     Cexp_if (Cexp_ispair fuel)
       (Cexp_if (Cexp_less n limit)
         (Cexp_pair n e)
         (candle_cv_nf_round_hi radix limit (Cexp_snd fuel)
           (Cexp_add (Cexp_div n radix)
             (Cexp_if (Cexp_eq (Cexp_mod n radix) (Cexp_num 0))
               (Cexp_num 0) (Cexp_num 1)))
           (Cexp_add e (Cexp_num 1))))
       (Cexp_pair n e)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_round_hi_def; cexp_if_def;
              cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_round_lo_correct = prove
 (`!fuel radix limit n e.
     candle_cv_nf_round_lo (Cexp_num radix) (Cexp_num limit)
       (candle_nf_fuel fuel) (Cexp_num n) (Cexp_num e) =
     candle_nf_pair (candle_nf_round_lo radix limit fuel n e)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_nf_fuel_def; candle_nf_round_lo_def;
                candle_cv_nf_round_lo_def; candle_nf_pair_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_fuel_def; candle_nf_round_lo_def;
                candle_cv_nf_round_lo_def; cexp_less_def] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def; candle_nf_pair_def;
                    cexp_div_def; cexp_add_def; ADD1]]);;

let candle_cv_nf_round_hi_correct = prove
 (`!fuel radix limit n e.
     candle_cv_nf_round_hi (Cexp_num radix) (Cexp_num limit)
       (candle_nf_fuel fuel) (Cexp_num n) (Cexp_num e) =
     candle_nf_pair (candle_nf_round_hi radix limit fuel n e)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_nf_fuel_def; candle_nf_round_hi_def;
                candle_cv_nf_round_hi_def; candle_nf_pair_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_fuel_def; candle_nf_round_hi_def;
                candle_cv_nf_round_hi_def; cexp_less_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def; candle_nf_pair_def] THEN
    REWRITE_TAC[cexp_div_def; cexp_mod_def; cexp_eq_def;
                injectivity "cval"] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def; cexp_add_def; ADD_CLAUSES; ADD1;
                    candle_nf_pair_def]]);;

let candle_cv_nf_round_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_round_lo_compute;
    candle_cv_nf_round_hi_compute];;

end;;
