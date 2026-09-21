(* ========================================================================== *)
(* Proof-producing folds over staged nonnegative native-float operations.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Multiplication and addition are rounded after *)
(* every step, so the reflected evaluator does not construct the enormous    *)
(* exact intermediate integers produced by the coarse polynomial evaluator.  *)
(* The ordinary folds retain explicit validity predicates for every supplied *)
(* exponent-alignment and scale witness.                                      *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_staged.ml";;

module Candle_cv_native_float_staged_fold = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_mul;;
open Candle_cv_native_float_staged;;

(* Each multiplication step carries its own rounding fuel and factor. *)
let candle_nf_staged_product_def = define
 `(candle_nf_staged_product radix scale limit
      ([]:(num list#(num#num))list) acc = acc) /\
  (candle_nf_staged_product radix scale limit (CONS h t) acc =
     candle_nf_staged_product radix scale limit t
       (candle_nf_scaled_mul_round_hi radix scale limit
         (FST h) acc (SND h)))`;;

let candle_nf_staged_product_valid_def = define
 `(candle_nf_staged_product_valid radix scale limit
      ([]:(num list#(num#num))list) acc <=> T) /\
  (candle_nf_staged_product_valid radix scale limit (CONS h t) acc <=>
     scale <= SND acc + SND (SND h) /\
     candle_nf_staged_product_valid radix scale limit t
       (candle_nf_scaled_mul_round_hi radix scale limit
         (FST h) acc (SND h)))`;;

let candle_nf_staged_product_value_def = define
 `(candle_nf_staged_product_value radix
      ([]:(num list#(num#num))list) = 1) /\
  (candle_nf_staged_product_value radix (CONS h t) =
     candle_nf_value radix (SND h) *
     candle_nf_staged_product_value radix t)`;;

let candle_nf_staged_product_bound_step = prove
 (`!a b c d e r n:num.
     a * b <= c * r /\ c * d <= e * n
     ==> a * (b * d) <= e * (r * n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((a:num) * b) * d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    MATCH_ACCEPT_TAC (AC MULT_AC `a * (b * d) = (a * b) * d:num`);
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((c:num) * r) * d` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_nf_le_mult_right THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((c:num) * d) * r` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC EQ_IMP_LE THEN
        MATCH_ACCEPT_TAC (AC MULT_AC `(c * r) * d = (c * d) * r:num`);
        MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((e:num) * n) * r` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_nf_le_mult_right THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC EQ_IMP_LE THEN
          MATCH_ACCEPT_TAC
           (AC MULT_AC `(e * n) * r = e * (r * n):num`)]]]]);;

let candle_nf_staged_product_sound = prove
 (`!steps radix scale limit acc.
     ~(radix = 0) /\
     candle_nf_staged_product_valid radix scale limit steps acc
     ==> candle_nf_value radix acc *
           candle_nf_staged_product_value radix steps <=
         candle_nf_value radix
           (candle_nf_staged_product radix scale limit steps acc) *
         (radix EXP scale) EXP LENGTH steps`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_product_def;
                candle_nf_staged_product_valid_def;
                candle_nf_staged_product_value_def; LENGTH; EXP;
                MULT_CLAUSES; LE_REFL];
    FIRST_X_ASSUM (LABEL_TAC "IH") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_product_def;
                candle_nf_staged_product_valid_def;
                candle_nf_staged_product_value_def; LENGTH; EXP] THEN
    STRIP_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`radix:num`; `scale:num`; `limit:num`;
           `FST (h:num list#(num#num))`;
           `acc:num#num`; `SND (h:num list#(num#num))`]
          candle_nf_scaled_mul_round_hi_sound)
        (CONJ
          (ASSUME `~(radix = 0)`)
          (ASSUME
            `scale <= SND (acc:num#num) +
               SND (SND (h:num list#(num#num)))`))) THEN
    DISCH_THEN (LABEL_TAC "HEAD") THEN
    USE_THEN "IH" (fun ih ->
      MP_TAC
       (MATCH_MP
         (SPECL
           [`radix:num`; `scale:num`; `limit:num`;
            `candle_nf_scaled_mul_round_hi radix scale limit
               (FST (h:num list#(num#num))) (acc:num#num) (SND h)`]
           ih)
         (CONJ
           (ASSUME `~(radix = 0)`)
           (ASSUME
             `candle_nf_staged_product_valid radix scale limit t
               (candle_nf_scaled_mul_round_hi radix scale limit
                  (FST (h:num list#(num#num))) (acc:num#num) (SND h))`)))) THEN
    DISCH_THEN (LABEL_TAC "TAIL") THEN
    USE_THEN "HEAD" (fun head ->
      USE_THEN "TAIL" (fun tail ->
        let inst =
          SPECL
              [`candle_nf_value radix (acc:num#num)`;
               `candle_nf_value radix
                  (SND (h:num list#(num#num)))`;
               `candle_nf_value radix
                  (candle_nf_scaled_mul_round_hi radix scale limit
                    (FST (h:num list#(num#num))) acc (SND h))`;
               `candle_nf_staged_product_value radix
                  (t:(num list#(num#num))list)`;
               `candle_nf_value radix
                  (candle_nf_staged_product radix scale limit t
                    (candle_nf_scaled_mul_round_hi radix scale limit
                      (FST (h:num list#(num#num))) acc (SND h)))`;
               `radix EXP scale`;
               `(radix EXP scale) EXP
                  LENGTH (t:(num list#(num#num))list)`]
              candle_nf_staged_product_bound_step in
        MATCH_ACCEPT_TAC (MATCH_MP inst (CONJ head tail))))]);;

let candle_nf_staged_product_step_def = new_definition
 `candle_nf_staged_product_step (step:num list#(num#num)) =
    Cexp_pair (candle_nf_fuel (FST step))
      (candle_nf_pair (SND step))`;;

let candle_nf_staged_product_steps_def = define
 `(candle_nf_staged_product_steps ([]:(num list#(num#num))list) =
     Cexp_num 0) /\
  (candle_nf_staged_product_steps (CONS h t) =
     Cexp_pair (candle_nf_staged_product_step h)
       (candle_nf_staged_product_steps t))`;;

let candle_cv_nf_staged_product_def = define
 `(candle_cv_nf_staged_product radix scale limit (Cexp_num z) acc = acc) /\
  (candle_cv_nf_staged_product radix scale limit (Cexp_pair h t) acc =
     candle_cv_nf_staged_product radix scale limit t
       (candle_cv_nf_scaled_mul_round_hi radix scale limit
         (Cexp_fst h) acc (Cexp_snd h)))`;;

let candle_cv_nf_staged_product_compute = prove
 (`!radix scale limit steps acc.
     candle_cv_nf_staged_product radix scale limit steps acc =
     Cexp_if (Cexp_ispair steps)
       (candle_cv_nf_staged_product radix scale limit (Cexp_snd steps)
         (candle_cv_nf_scaled_mul_round_hi radix scale limit
           (Cexp_fst (Cexp_fst steps)) acc
           (Cexp_snd (Cexp_fst steps))))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `steps:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_staged_product_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_staged_product_correct = prove
 (`!steps radix scale limit acc.
     candle_cv_nf_staged_product
       (Cexp_num radix) (Cexp_num scale) (Cexp_num limit)
       (candle_nf_staged_product_steps steps) (candle_nf_pair acc) =
     candle_nf_pair
       (candle_nf_staged_product radix scale limit steps acc)`,
  LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[candle_nf_staged_product_steps_def;
                  candle_nf_staged_product_step_def;
                  candle_nf_staged_product_def;
                  candle_cv_nf_staged_product_def;
                  cexp_fst_def; cexp_snd_def;
                  candle_cv_nf_scaled_mul_round_hi_correct]);;

(* Each addition step carries round fuel, exact alignment fuel, and one term. *)
let candle_nf_staged_sum_def = define
 `(candle_nf_staged_sum radix limit
      ([]:(num list#(num list#(num#num)))list) acc = acc) /\
  (candle_nf_staged_sum radix limit (CONS h t) acc =
     candle_nf_staged_sum radix limit t
       (candle_nf_add_round_hi radix limit (FST h) (FST (SND h))
         acc (SND (SND h))))`;;

let candle_nf_staged_sum_valid_def = define
 `(candle_nf_staged_sum_valid radix limit
      ([]:(num list#(num list#(num#num)))list) acc <=> T) /\
  (candle_nf_staged_sum_valid radix limit (CONS h t) acc <=>
     candle_nf_add_power_complete (FST (SND h)) acc (SND (SND h)) /\
     candle_nf_staged_sum_valid radix limit t
       (candle_nf_add_round_hi radix limit (FST h) (FST (SND h))
         acc (SND (SND h))))`;;

let candle_nf_staged_sum_value_def = define
 `(candle_nf_staged_sum_value radix
      ([]:(num list#(num list#(num#num)))list) = 0) /\
  (candle_nf_staged_sum_value radix (CONS h t) =
     candle_nf_value radix (SND (SND h)) +
     candle_nf_staged_sum_value radix t)`;;

let candle_nf_staged_sum_bound_step = prove
 (`!a b c d e:num. a + b <= c /\ c + d <= e ==> a + (b + d) <= e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `((a:num) + b) + d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    MATCH_ACCEPT_TAC (AC ADD_AC `a + (b + d) = (a + b) + d:num`);
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(c:num) + d` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[LE_REFL];
      ASM_REWRITE_TAC[]]]);;

let candle_nf_staged_sum_sound = prove
 (`!steps radix limit acc.
     ~(radix = 0) /\ candle_nf_staged_sum_valid radix limit steps acc
     ==> candle_nf_value radix acc +
           candle_nf_staged_sum_value radix steps <=
         candle_nf_value radix
           (candle_nf_staged_sum radix limit steps acc)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_sum_def;
                candle_nf_staged_sum_valid_def;
                candle_nf_staged_sum_value_def; ADD_CLAUSES; LE_REFL];
    FIRST_X_ASSUM (LABEL_TAC "IH") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_sum_def;
                candle_nf_staged_sum_valid_def;
                candle_nf_staged_sum_value_def] THEN
    STRIP_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`radix:num`; `limit:num`;
           `FST (h:num list#(num list#(num#num)))`;
           `FST (SND (h:num list#(num list#(num#num))))`;
           `acc:num#num`;
           `SND (SND (h:num list#(num list#(num#num))))`]
          candle_nf_add_round_hi_sound)
        (CONJ
          (ASSUME `~(radix = 0)`)
          (ASSUME
            `candle_nf_add_power_complete
               (FST (SND (h:num list#(num list#(num#num)))))
               (acc:num#num) (SND (SND h))`))) THEN
    DISCH_THEN (LABEL_TAC "HEAD") THEN
    USE_THEN "IH" (fun ih ->
      MP_TAC
       (MATCH_MP
         (SPECL
           [`radix:num`; `limit:num`;
            `candle_nf_add_round_hi radix limit
               (FST (h:num list#(num list#(num#num))))
               (FST (SND h)) (acc:num#num) (SND (SND h))`]
           ih)
         (CONJ
           (ASSUME `~(radix = 0)`)
           (ASSUME
             `candle_nf_staged_sum_valid radix limit t
                (candle_nf_add_round_hi radix limit
                  (FST (h:num list#(num list#(num#num))))
                  (FST (SND h)) (acc:num#num)
                  (SND (SND h)))`)))) THEN
    DISCH_THEN (LABEL_TAC "TAIL") THEN
    USE_THEN "HEAD" (fun head ->
      USE_THEN "TAIL" (fun tail ->
        MATCH_ACCEPT_TAC
          (MATCH_MP
            (SPECL
              [`candle_nf_value radix (acc:num#num)`;
               `candle_nf_value radix
                  (SND (SND
                    (h:num list#(num list#(num#num)))))`;
               `candle_nf_value radix
                  (candle_nf_add_round_hi radix limit
                    (FST (h:num list#(num list#(num#num))))
                    (FST (SND h)) acc (SND (SND h)))`;
               `candle_nf_staged_sum_value radix
                  (t:(num list#(num list#(num#num)))list)`;
               `candle_nf_value radix
                  (candle_nf_staged_sum radix limit t
                    (candle_nf_add_round_hi radix limit
                      (FST (h:num list#(num list#(num#num))))
                      (FST (SND h)) acc (SND (SND h))))`]
              candle_nf_staged_sum_bound_step)
            (CONJ head tail))))]);;

let candle_nf_staged_sum_step_def = new_definition
 `candle_nf_staged_sum_step
      (step:num list#(num list#(num#num))) =
    Cexp_pair (candle_nf_fuel (FST step))
      (Cexp_pair (candle_nf_fuel (FST (SND step)))
        (candle_nf_pair (SND (SND step))))`;;

let candle_nf_staged_sum_steps_def = define
 `(candle_nf_staged_sum_steps
      ([]:(num list#(num list#(num#num)))list) = Cexp_num 0) /\
  (candle_nf_staged_sum_steps (CONS h t) =
     Cexp_pair (candle_nf_staged_sum_step h)
       (candle_nf_staged_sum_steps t))`;;

let candle_cv_nf_staged_sum_def = define
 `(candle_cv_nf_staged_sum radix limit (Cexp_num z) acc = acc) /\
  (candle_cv_nf_staged_sum radix limit (Cexp_pair h t) acc =
     candle_cv_nf_staged_sum radix limit t
       (candle_cv_nf_add_round_hi radix limit
         (Cexp_fst h) (Cexp_fst (Cexp_snd h)) acc
         (Cexp_snd (Cexp_snd h))))`;;

let candle_cv_nf_staged_sum_compute = prove
 (`!radix limit steps acc.
     candle_cv_nf_staged_sum radix limit steps acc =
     Cexp_if (Cexp_ispair steps)
       (candle_cv_nf_staged_sum radix limit (Cexp_snd steps)
         (candle_cv_nf_add_round_hi radix limit
           (Cexp_fst (Cexp_fst steps))
           (Cexp_fst (Cexp_snd (Cexp_fst steps))) acc
           (Cexp_snd (Cexp_snd (Cexp_fst steps)))))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `steps:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_staged_sum_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_staged_sum_correct = prove
 (`!steps radix limit acc.
     candle_cv_nf_staged_sum (Cexp_num radix) (Cexp_num limit)
       (candle_nf_staged_sum_steps steps) (candle_nf_pair acc) =
     candle_nf_pair (candle_nf_staged_sum radix limit steps acc)`,
  LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[candle_nf_staged_sum_steps_def;
                  candle_nf_staged_sum_step_def;
                  candle_nf_staged_sum_def;
                  candle_cv_nf_staged_sum_def;
                  cexp_fst_def; cexp_snd_def;
                  candle_cv_nf_add_round_hi_correct]);;

let candle_cv_nf_staged_fold_compute_eqs =
  map SPEC_ALL
   [candle_cv_nf_staged_product_compute;
    candle_cv_nf_staged_sum_compute] @
  candle_cv_nf_staged_compute_eqs;;

end;;
