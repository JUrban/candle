(* ========================================================================== *)
(* Verified reduction for reflected exact rationals.                         *)
(*                                                                            *)
(* The bounded Euclidean pass is only a candidate generator.  Before using   *)
(* its proposed divisor, the reflected program checks the three exact        *)
(* multiplication identities and a nonzero quotient.  A bad candidate or     *)
(* exhausted fuel therefore falls back to the unreduced rational.             *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_core.ml";;
needs "candle/cv_compute_exact_interval_core.ml";;
needs "candle/cv_compute_linear_combination_normalize.ml";;

module Candle_cv_exact_rational_normalize = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_linear_combination_normalize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;

(* -------------------------------------------------------------------------- *)
(* Ordinary bounded candidate generator and checked normalization.            *)
(* -------------------------------------------------------------------------- *)

let candle_num_gcd_fuel_def = define
 `(candle_num_gcd_fuel 0 a b = 1) /\
  (candle_num_gcd_fuel (SUC fuel) a b =
     if b = 0 then a else candle_num_gcd_fuel fuel b (a MOD b))`;;

let candle_num_gcd_def =
  let fuel_count =
    itlist (fun _ tail -> mk_comb (`SUC`,tail)) (0--127) `0` in
  new_definition
    (mk_eq
      (`(candle_num_gcd (a:num) (b:num)):num`,
       list_mk_comb
        (`candle_num_gcd_fuel`,[fuel_count;`a:num`;`b:num`])));;

let candle_q_normalize_fallback_def = new_definition
 `candle_q_normalize_fallback (z:num#num) denominator =
    (z,denominator - 1)`;;

let candle_q_normalize_divide_def = new_definition
 `candle_q_normalize_divide (z:num#num) denominator common =
    ((FST z DIV common,SND z DIV common),
     denominator DIV common - 1)`;;

let candle_q_normalize_verified_def = new_definition
 `candle_q_normalize_verified (z:num#num) denominator common =
    if common = 0 then candle_q_normalize_fallback z denominator
    else if denominator DIV common = 0 then
      candle_q_normalize_fallback z denominator
    else if (FST z DIV common) * common = FST z then
      if (SND z DIV common) * common = SND z then
        if (denominator DIV common) * common = denominator then
          candle_q_normalize_divide z denominator common
        else candle_q_normalize_fallback z denominator
      else candle_q_normalize_fallback z denominator
    else candle_q_normalize_fallback z denominator`;;

let candle_q_normalize_signed_def = new_definition
 `candle_q_normalize_signed (z:num#num) denominator =
    candle_q_normalize_verified z denominator
      (candle_num_gcd (FST z + SND z) denominator)`;;

let candle_q_normalize_def = new_definition
 `candle_q_normalize (q:(num#num)#num) =
    candle_q_normalize_signed
      (candle_lc_znormalize (FST q)) (candle_q_den q)`;;

let candle_q_add_normalized_def = new_definition
 `candle_q_add_normalized x y = candle_q_normalize (candle_q_add x y)`;;

let candle_q_mul_normalized_def = new_definition
 `candle_q_mul_normalized x y = candle_q_normalize (candle_q_mul x y)`;;

let candle_q_interval_normalize_def = new_definition
 `candle_q_interval_normalize
    (i:((num#num)#num)#((num#num)#num)) =
    (candle_q_normalize (FST i),candle_q_normalize (SND i))`;;

let candle_q_real_normalize_fallback = prove
 (`!z denominator.
     ~(denominator = 0)
     ==> candle_q_real (candle_q_normalize_fallback z denominator) =
         candle_lc_zreal z / &denominator`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_normalize_fallback_def;
              candle_q_den_def; FST; SND] THEN
  SUBGOAL_THEN `SUC (denominator - 1) = denominator` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REFL_TAC]);;

let candle_q_real_normalize_divide = prove
 (`!z:num#num. !denominator common:num.
     ~(common = 0) /\
     ~(denominator DIV common = 0) /\
     (FST z DIV common) * common = FST z /\
     (SND z DIV common) * common = SND z /\
     (denominator DIV common) * common = denominator
     ==> candle_q_real (candle_q_normalize_divide z denominator common) =
         candle_lc_zreal z / &denominator`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[candle_q_real_def; candle_q_normalize_divide_def;
              candle_q_den_def; candle_lc_zreal_def; FST; SND] THEN
  SUBGOAL_THEN
   `SUC (denominator DIV common - 1) = denominator DIV common`
  SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((&(common:num):real) = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~((&(denominator DIV common):real) = &0)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(FST (z:num#num)):real) = &(FST z DIV common) * &common`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(SND (z:num#num)):real) = &(SND z DIV common) * &common`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(denominator:num):real) =
    &(denominator DIV common) * &common`
  (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC
    (REAL_FIELD
      `!a b c d:real.
         ~(c = &0) /\ ~(d = &0)
         ==> (a - b) / d = (a * c - b * c) / (d * c)`) THEN
  ASM_REWRITE_TAC[]);;

let candle_q_real_normalize_verified = prove
 (`!z denominator common.
     ~(denominator = 0)
     ==> candle_q_real
           (candle_q_normalize_verified z denominator common) =
         candle_lc_zreal z / &denominator`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[candle_q_normalize_verified_def] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  FIRST
   [MATCH_MP_TAC candle_q_real_normalize_divide THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC candle_q_real_normalize_fallback THEN ASM_REWRITE_TAC[]]);;

let candle_q_real_normalize_signed = prove
 (`!z denominator.
     ~(denominator = 0)
     ==> candle_q_real (candle_q_normalize_signed z denominator) =
         candle_lc_zreal z / &denominator`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[candle_q_normalize_signed_def] THEN
  MATCH_MP_TAC candle_q_real_normalize_verified THEN
  ASM_REWRITE_TAC[]);;

let candle_q_real_normalize = prove
 (`!q. candle_q_real (candle_q_normalize q) = candle_q_real q`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_q_normalize_def] THEN
  SIMP_TAC[candle_q_real_normalize_signed; NOT_SUC;
           candle_q_real_def; candle_q_den_def; FST; SND;
           candle_lc_zreal_normalize]);;

let candle_q_real_add_normalized = prove
 (`!x y.
     candle_q_real (candle_q_add_normalized x y) =
     candle_q_real x + candle_q_real y`,
  REWRITE_TAC[candle_q_add_normalized_def; candle_q_real_normalize;
              candle_q_real_add]);;

let candle_q_real_mul_normalized = prove
 (`!x y.
     candle_q_real (candle_q_mul_normalized x y) =
     candle_q_real x * candle_q_real y`,
  REWRITE_TAC[candle_q_mul_normalized_def; candle_q_real_normalize;
              candle_q_real_mul]);;

(* -------------------------------------------------------------------------- *)
(* Reflected implementation and representation theorem.                       *)
(* -------------------------------------------------------------------------- *)

let candle_cv_num_fuel_def = define
 `(candle_cv_num_fuel 0 = Cexp_num 0) /\
  (candle_cv_num_fuel (SUC n) =
     Cexp_pair (Cexp_num 0) (candle_cv_num_fuel n))`;;

let candle_cv_num_gcd_fuel_def = define
 `(candle_cv_num_gcd_fuel (Cexp_num n) a b = Cexp_num 1) /\
  (candle_cv_num_gcd_fuel (Cexp_pair h t) a b =
     Cexp_if (Cexp_eq b (Cexp_num 0)) a
       (candle_cv_num_gcd_fuel t b (Cexp_mod a b)))`;;

let candle_cv_num_gcd_fuel_compute = prove
 (`!fuel a b.
     candle_cv_num_gcd_fuel fuel a b =
     Cexp_if (Cexp_ispair fuel)
       (Cexp_if (Cexp_eq b (Cexp_num 0)) a
         (candle_cv_num_gcd_fuel
           (Cexp_snd fuel) b (Cexp_mod a b)))
       (Cexp_num 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_num_gcd_fuel_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_num_gcd_def =
  let fuel =
    itlist
      (fun _ tail -> list_mk_comb (`Cexp_pair`,[`Cexp_num 0`;tail]))
      (0--127) `Cexp_num 0` in
  new_definition
    (mk_eq
      (`(candle_cv_num_gcd (a:cval) (b:cval)):cval`,
       list_mk_comb (`candle_cv_num_gcd_fuel`,[fuel;`a:cval`;`b:cval`])));;

let candle_cv_q_normalize_fallback_def = new_definition
 `candle_cv_q_normalize_fallback z denominator =
    Cexp_pair z (Cexp_sub denominator (Cexp_num 1))`;;

let candle_cv_q_normalize_divide_def = new_definition
 `candle_cv_q_normalize_divide z denominator common =
    Cexp_pair
      (Cexp_pair
        (Cexp_div (Cexp_fst z) common)
        (Cexp_div (Cexp_snd z) common))
      (Cexp_sub (Cexp_div denominator common) (Cexp_num 1))`;;

let candle_cv_q_normalize_verified_def = new_definition
 `candle_cv_q_normalize_verified z denominator common =
    Cexp_if (Cexp_eq common (Cexp_num 0))
      (candle_cv_q_normalize_fallback z denominator)
      (Cexp_if
        (Cexp_eq (Cexp_div denominator common) (Cexp_num 0))
        (candle_cv_q_normalize_fallback z denominator)
        (Cexp_if
          (Cexp_eq
            (Cexp_mul (Cexp_div (Cexp_fst z) common) common)
            (Cexp_fst z))
          (Cexp_if
            (Cexp_eq
              (Cexp_mul (Cexp_div (Cexp_snd z) common) common)
              (Cexp_snd z))
            (Cexp_if
              (Cexp_eq
                (Cexp_mul (Cexp_div denominator common) common)
                denominator)
              (candle_cv_q_normalize_divide z denominator common)
              (candle_cv_q_normalize_fallback z denominator))
            (candle_cv_q_normalize_fallback z denominator))
          (candle_cv_q_normalize_fallback z denominator)))`;;

let candle_cv_q_normalize_signed_def = new_definition
 `candle_cv_q_normalize_signed z denominator =
    candle_cv_q_normalize_verified z denominator
      (candle_cv_num_gcd
        (Cexp_add (Cexp_fst z) (Cexp_snd z)) denominator)`;;

let candle_cv_q_normalize_def = new_definition
 `candle_cv_q_normalize q =
    candle_cv_q_normalize_signed
      (candle_cv_lc_znormalize (Cexp_fst q))
      (candle_cv_q_den q)`;;

let candle_cv_q_add_normalized_def = new_definition
 `candle_cv_q_add_normalized x y =
    candle_cv_q_normalize (candle_cv_q_add x y)`;;

let candle_cv_q_mul_normalized_def = new_definition
 `candle_cv_q_mul_normalized x y =
    candle_cv_q_normalize (candle_cv_q_mul x y)`;;

let candle_cv_q_interval_normalize_def = new_definition
 `candle_cv_q_interval_normalize i =
    Cexp_pair
      (candle_cv_q_normalize (Cexp_fst i))
      (candle_cv_q_normalize (Cexp_snd i))`;;

let candle_cv_q_normalized_compute_eqs =
  map SPEC_ALL
   [candle_cv_lc_znormalize_def;
    candle_cv_num_gcd_fuel_compute;
    candle_cv_num_gcd_def;
    candle_cv_q_normalize_fallback_def;
    candle_cv_q_normalize_divide_def;
    candle_cv_q_normalize_verified_def;
    candle_cv_q_normalize_signed_def;
    candle_cv_q_normalize_def;
    candle_cv_q_add_normalized_def;
    candle_cv_q_mul_normalized_def;
    candle_cv_q_interval_normalize_def];;

let candle_cv_num_gcd_fuel_correct = prove
 (`!fuel a b.
     candle_cv_num_gcd_fuel
       (candle_cv_num_fuel fuel) (Cexp_num a) (Cexp_num b) =
     Cexp_num (candle_num_gcd_fuel fuel a b)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[candle_cv_num_fuel_def; candle_cv_num_gcd_fuel_def;
                candle_num_gcd_fuel_def];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_cv_num_fuel_def; candle_cv_num_gcd_fuel_def;
                candle_num_gcd_fuel_def; cexp_eq_def; injectivity "cval";
                cexp_mod_def] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[cexp_if_def]]);;

let candle_cv_num_fuel_128 =
  let fuel_count =
    itlist (fun _ tail -> mk_comb (`SUC`,tail)) (0--127) `0`
  and fuel =
    itlist
      (fun _ tail -> list_mk_comb (`Cexp_pair`,[`Cexp_num 0`;tail]))
      (0--127) `Cexp_num 0` in
  prove
   (mk_eq (mk_comb (`candle_cv_num_fuel`,fuel_count),fuel),
    REWRITE_TAC[candle_cv_num_fuel_def]);;

let candle_cv_num_gcd_correct = prove
 (`!a b.
     candle_cv_num_gcd (Cexp_num a) (Cexp_num b) =
     Cexp_num (candle_num_gcd a b)`,
  REWRITE_TAC[candle_cv_num_gcd_def; candle_num_gcd_def;
              GSYM candle_cv_num_fuel_128;
              candle_cv_num_gcd_fuel_correct]);;

let candle_cv_q_normalize_fallback_correct = prove
 (`!z denominator.
     candle_cv_q_normalize_fallback
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_q (candle_q_normalize_fallback z denominator)`,
  REWRITE_TAC[candle_cv_q_normalize_fallback_def;
              candle_q_normalize_fallback_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_sub_def; FST; SND]);;

let candle_cv_q_normalize_divide_correct = prove
 (`!z denominator common.
     candle_cv_q_normalize_divide
       (candle_cv_lc_z z) (Cexp_num denominator) (Cexp_num common) =
     candle_cv_q (candle_q_normalize_divide z denominator common)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_divide_def;
              candle_q_normalize_divide_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_div_def; cexp_sub_def;
              FST; SND]);;

let candle_cv_q_normalize_verified_correct = prove
 (`!z denominator common.
     candle_cv_q_normalize_verified
       (candle_cv_lc_z z) (Cexp_num denominator) (Cexp_num common) =
     candle_cv_q (candle_q_normalize_verified z denominator common)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_verified_def;
              candle_q_normalize_verified_def;
              candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_div_def; cexp_mul_def; cexp_eq_def;
              injectivity "cval"] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[cexp_if_def]) THEN
  REWRITE_TAC[candle_cv_q_normalize_fallback_def;
              candle_q_normalize_fallback_def;
              candle_cv_q_normalize_divide_def;
              candle_q_normalize_divide_def;
              candle_cv_q_def; candle_cv_lc_z_def;
              cexp_fst_def; cexp_snd_def; cexp_div_def; cexp_sub_def;
              FST; SND]);;

let candle_cv_num_gcd_signed_correct = prove
 (`!z denominator.
     candle_cv_num_gcd
       (Cexp_add
         (Cexp_fst (candle_cv_lc_z z))
         (Cexp_snd (candle_cv_lc_z z)))
       (Cexp_num denominator) =
     Cexp_num (candle_num_gcd (FST z + SND z) denominator)`,
  REWRITE_TAC[candle_cv_lc_z_def; cexp_fst_def; cexp_snd_def;
              cexp_add_def; candle_cv_num_gcd_correct]);;

let candle_cv_q_normalize_signed_correct = prove
 (`!z denominator.
     candle_cv_q_normalize_signed
       (candle_cv_lc_z z) (Cexp_num denominator) =
     candle_cv_q (candle_q_normalize_signed z denominator)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_signed_def;
              candle_q_normalize_signed_def;
              candle_cv_num_gcd_signed_correct;
              candle_cv_q_normalize_verified_correct]);;

let candle_cv_q_normalize_correct = prove
 (`!q.
     candle_cv_q_normalize (candle_cv_q q) =
     candle_cv_q (candle_q_normalize q)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_normalize_def; candle_q_normalize_def;
              candle_cv_q_def; cexp_fst_def;
              candle_cv_lc_znormalize_correct;
              candle_cv_q_den_correct;
              candle_cv_q_normalize_signed_correct]);;

let candle_cv_q_add_normalized_correct = prove
 (`!x y.
     candle_cv_q_add_normalized (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_add_normalized x y)`,
  REWRITE_TAC[candle_cv_q_add_normalized_def;
              candle_q_add_normalized_def;
              candle_cv_q_add_correct; candle_cv_q_normalize_correct]);;

let candle_cv_q_mul_normalized_correct = prove
 (`!x y.
     candle_cv_q_mul_normalized (candle_cv_q x) (candle_cv_q y) =
     candle_cv_q (candle_q_mul_normalized x y)`,
  REWRITE_TAC[candle_cv_q_mul_normalized_def;
              candle_q_mul_normalized_def;
              candle_cv_q_mul_correct; candle_cv_q_normalize_correct]);;

let candle_cv_q_interval_normalize_correct = prove
 (`!i.
     candle_cv_q_interval_normalize (candle_cv_q_interval i) =
     candle_cv_q_interval (candle_q_interval_normalize i)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_q_interval_normalize_def;
              candle_q_interval_normalize_def;
              candle_cv_q_interval_def; cexp_fst_def; cexp_snd_def;
              candle_cv_q_normalize_correct; FST; SND]);;

end;;
