(* ========================================================================== *)
(* Single-verdict reflected native-float polynomial checker.                  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. The computed value is one Boolean cval rather   *)
(* than a list of rounded results.  Its soundness theorem relates the exact   *)
(* source polynomials and thresholds, so successful computation can be used   *)
(* without trusting the OCaml wrapper or materializing one result theorem per  *)
(* polynomial.                                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_batch.ml";;

module Candle_cv_native_float_checker = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_polynomial;;
open Candle_cv_native_float_batch;;

let candle_nf_fueled_batch_check_hi_def = define
 `(candle_nf_fueled_batch_check_hi radix
      ([]:num list) ([]:(num#(num list#num list)list)list) <=> T) /\
  (candle_nf_fueled_batch_check_hi radix [] (CONS job jobs) <=> F) /\
  (candle_nf_fueled_batch_check_hi radix (CONS bound bounds) [] <=> F) /\
  (candle_nf_fueled_batch_check_hi radix (CONS bound bounds)
      (CONS job jobs) <=>
     candle_nf_fueled_sum radix (SND job) < SUC bound /\
     candle_nf_fueled_batch_check_hi radix bounds jobs)`;;

let candle_nf_batch_threshold_upper_def = define
 `(candle_nf_batch_threshold_upper radix
      ([]:(num#((num#num)list)list)list) ([]:num list) <=> T) /\
  (candle_nf_batch_threshold_upper radix [] (CONS bound bounds) <=> F) /\
  (candle_nf_batch_threshold_upper radix (CONS source sources) [] <=> F) /\
  (candle_nf_batch_threshold_upper radix (CONS source sources)
      (CONS bound bounds) <=>
     candle_nf_polynomial_value radix (SND source) <=
       bound * radix EXP FST source /\
     candle_nf_batch_threshold_upper radix sources bounds)`;;

let candle_nf_fueled_threshold_upper = prove
 (`!terms items radix target bound.
     candle_nf_fueled_alignment target terms items /\
     candle_nf_fueled_sum radix items < SUC bound
     ==> candle_nf_polynomial_value radix terms <=
         bound * radix EXP target`,
  MESON_TAC[candle_nf_fueled_sum_value;LE_MULT2;
    ARITH_RULE `m < SUC n ==> m <= n`;LE_REFL]);;

let candle_nf_fueled_batch_check_hi_sound = prove
 (`!sources jobs bounds radix.
     candle_nf_fueled_batch_alignment sources jobs /\
     candle_nf_fueled_batch_check_hi radix bounds jobs
     ==> candle_nf_batch_threshold_upper radix sources bounds`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `jobs:(num#(num list#num list)list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    MP_TAC (ISPEC `bounds:num list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_batch_alignment_def;
                candle_nf_fueled_batch_check_hi_def;
                candle_nf_batch_threshold_upper_def];
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `jobs:(num#(num list#num list)list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    MP_TAC (ISPEC `bounds:num list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_batch_alignment_def;
                candle_nf_fueled_batch_check_hi_def;
                candle_nf_batch_threshold_upper_def] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[candle_nf_fueled_threshold_upper];
      ASM_MESON_TAC[]]]);;

let candle_cv_nf_fueled_batch_check_hi_def = define
  `(candle_cv_nf_fueled_batch_check_hi radix
      (Cexp_num z) (Cexp_num w) = Cexp_num 1) /\
  (candle_cv_nf_fueled_batch_check_hi radix
      (Cexp_num z) (Cexp_pair job jobs) = Cexp_num 0) /\
  (candle_cv_nf_fueled_batch_check_hi radix
      (Cexp_pair bound bounds) (Cexp_num z) = Cexp_num 0) /\
  (candle_cv_nf_fueled_batch_check_hi radix
      (Cexp_pair bound bounds) (Cexp_pair job jobs) =
     Cexp_if
       (Cexp_less
         (candle_cv_nf_fueled_sum radix (Cexp_snd job))
         (Cexp_add bound (Cexp_num 1)))
       (candle_cv_nf_fueled_batch_check_hi radix bounds jobs)
       (Cexp_num 0))`;;

let candle_cv_nf_fueled_batch_check_hi_compute = prove
 (`!radix bounds jobs.
     candle_cv_nf_fueled_batch_check_hi radix bounds jobs =
     Cexp_if (Cexp_ispair bounds)
       (Cexp_if (Cexp_ispair jobs)
         (Cexp_if
           (Cexp_less
             (candle_cv_nf_fueled_sum radix
               (Cexp_snd (Cexp_fst jobs)))
             (Cexp_add (Cexp_fst bounds) (Cexp_num 1)))
           (candle_cv_nf_fueled_batch_check_hi radix
             (Cexp_snd bounds) (Cexp_snd jobs))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_if (Cexp_ispair jobs) (Cexp_num 0) (Cexp_num 1))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `bounds:cval` (cases "cval")) THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_fueled_batch_check_hi_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_bool_and = prove
 (`!p q.
     Cexp_if (Cexp_num (if p then SUC 0 else 0))
       (Cexp_num (if q then SUC 0 else 0)) (Cexp_num 0) =
     Cexp_num (if p /\ q then SUC 0 else 0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `p:bool` THEN
  BOOL_CASES_TAC `q:bool` THEN REWRITE_TAC[cexp_if_def]);;

let candle_cv_nf_fueled_batch_check_hi_correct = prove
 (`!bounds jobs radix.
     candle_cv_nf_fueled_batch_check_hi (Cexp_num radix)
       (candle_nf_num_list bounds) (candle_nf_fueled_jobs jobs) =
     Cexp_num
       (if candle_nf_fueled_batch_check_hi radix bounds jobs
        then SUC 0 else 0)`,
  LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `jobs:(num#(num list#num list)list)list` list_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_ALL_TAC
      (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
  ASM_REWRITE_TAC[candle_nf_num_list_def; candle_nf_fueled_jobs_def;
                  candle_nf_fueled_job_def;
                  candle_nf_fueled_batch_check_hi_def;
                  candle_cv_nf_fueled_batch_check_hi_def;
                  candle_cv_nf_fueled_sum_correct;
                  cexp_fst_def; cexp_snd_def; cexp_add_def;
                  cexp_less_def;
                  ARITH_RULE `m < SUC n <=> m < n + 1`] THEN
  REWRITE_TAC[candle_cv_nf_bool_and] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_cv_nf_fueled_batch_checker_compute_eqs =
  map SPEC_ALL [candle_cv_nf_fueled_batch_check_hi_compute] @
  candle_cv_nf_fueled_polynomial_compute_eqs;;

end;;
