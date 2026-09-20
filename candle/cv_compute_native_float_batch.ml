(* ========================================================================== *)
(* Batched reflected native-float polynomial bounds.                           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Multiple independently aligned nonnegative      *)
(* polynomials are evaluated behind one Kernel.compute call.  The ordinary    *)
(* specification retains every source polynomial and proves a pointwise upper *)
(* bound for the complete result list.                                         *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_polynomial.ml";;

module Candle_cv_native_float_batch = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_polynomial;;

let candle_nf_fueled_batch_round_hi_def = define
 `(candle_nf_fueled_batch_round_hi radix limit fuel
      ([]:(num#(num list#num list)list)list) = ([]:(num#num)list)) /\
  (candle_nf_fueled_batch_round_hi radix limit fuel (CONS h t) =
     CONS
       (candle_nf_fueled_polynomial_round_hi
          radix limit fuel (FST h) (SND h))
       (candle_nf_fueled_batch_round_hi radix limit fuel t))`;;

let candle_nf_fueled_batch_alignment_def = define
 `(candle_nf_fueled_batch_alignment
      ([]:(num#((num#num)list)list)list)
      ([]:(num#(num list#num list)list)list) <=> T) /\
  (candle_nf_fueled_batch_alignment [] (CONS job jobs) <=> F) /\
  (candle_nf_fueled_batch_alignment (CONS source sources) [] <=> F) /\
  (candle_nf_fueled_batch_alignment (CONS source sources)
      (CONS job jobs) <=>
     FST source = FST job /\
     candle_nf_fueled_alignment
       (FST source) (SND source) (SND job) /\
     candle_nf_fueled_batch_alignment sources jobs)`;;

let candle_nf_batch_upper_def = define
 `(candle_nf_batch_upper radix
      ([]:(num#((num#num)list)list)list) ([]:(num#num)list) <=> T) /\
  (candle_nf_batch_upper radix [] (CONS result results) <=> F) /\
  (candle_nf_batch_upper radix (CONS source sources) [] <=> F) /\
  (candle_nf_batch_upper radix (CONS source sources)
      (CONS result results) <=>
     candle_nf_polynomial_value radix (SND source) <=
       FST result * radix EXP SND result /\
     candle_nf_batch_upper radix sources results)`;;

let candle_nf_fueled_batch_round_hi_sound = prove
 (`!sources jobs fuel radix limit.
     ~(radix = 0) /\ candle_nf_fueled_batch_alignment sources jobs
     ==> candle_nf_batch_upper radix sources
           (candle_nf_fueled_batch_round_hi radix limit fuel jobs)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC
      (ISPEC `jobs:(num#(num list#num list)list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_batch_alignment_def;
                candle_nf_fueled_batch_round_hi_def;
                candle_nf_batch_upper_def];
    REPEAT GEN_TAC THEN
    MP_TAC
      (ISPEC `jobs:(num#(num list#num list)list)list` list_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_ALL_TAC
        (CHOOSE_THEN (CHOOSE_THEN SUBST_ALL_TAC))) THEN
    REWRITE_TAC[candle_nf_fueled_batch_alignment_def;
                candle_nf_fueled_batch_round_hi_def;
                candle_nf_batch_upper_def] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[candle_nf_fueled_polynomial_round_hi_sound];
      ASM_MESON_TAC[]]]);;

let candle_nf_fueled_job_def = new_definition
 `candle_nf_fueled_job (job:num#(num list#num list)list) =
    Cexp_pair (Cexp_num (FST job))
      (candle_nf_fueled_items (SND job))`;;

let candle_nf_fueled_jobs_def = define
 `(candle_nf_fueled_jobs ([]:(num#(num list#num list)list)list) =
     Cexp_num 0) /\
  (candle_nf_fueled_jobs (CONS h t) =
     Cexp_pair (candle_nf_fueled_job h)
       (candle_nf_fueled_jobs t))`;;

let candle_nf_pairs_def = define
 `(candle_nf_pairs ([]:(num#num)list) = Cexp_num 0) /\
  (candle_nf_pairs (CONS h t) =
     Cexp_pair (candle_nf_pair h) (candle_nf_pairs t))`;;

let candle_nf_decode_pairs_def = define
 `(candle_nf_decode_pairs (Cexp_num z) = ([]:(num#num)list)) /\
  (candle_nf_decode_pairs (Cexp_pair h t) =
     CONS (candle_nf_decode_pair h) (candle_nf_decode_pairs t))`;;

let candle_nf_pairs_roundtrip = prove
 (`!xs:(num#num)list.
     candle_nf_decode_pairs (candle_nf_pairs xs) = xs`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_pairs_def; candle_nf_decode_pairs_def;
                  candle_nf_pair_roundtrip]);;

let candle_cv_nf_fueled_batch_round_hi_def = define
 `(candle_cv_nf_fueled_batch_round_hi radix limit fuel (Cexp_num z) =
     Cexp_num 0) /\
  (candle_cv_nf_fueled_batch_round_hi radix limit fuel (Cexp_pair h t) =
     Cexp_pair
       (candle_cv_nf_fueled_polynomial_round_hi
          radix limit fuel (Cexp_fst h) (Cexp_snd h))
       (candle_cv_nf_fueled_batch_round_hi radix limit fuel t))`;;

let candle_cv_nf_fueled_batch_round_hi_compute = prove
 (`!radix limit fuel jobs.
     candle_cv_nf_fueled_batch_round_hi radix limit fuel jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_nf_fueled_polynomial_round_hi
           radix limit fuel
           (Cexp_fst (Cexp_fst jobs))
           (Cexp_snd (Cexp_fst jobs)))
         (candle_cv_nf_fueled_batch_round_hi
           radix limit fuel (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_fueled_batch_round_hi_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_nf_fueled_batch_round_hi_correct = prove
 (`!jobs fuel radix limit.
     candle_cv_nf_fueled_batch_round_hi
       (Cexp_num radix) (Cexp_num limit) (candle_nf_fuel fuel)
       (candle_nf_fueled_jobs jobs) =
     candle_nf_pairs
       (candle_nf_fueled_batch_round_hi radix limit fuel jobs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_nf_fueled_jobs_def; candle_nf_fueled_job_def;
                  candle_nf_pairs_def;
                  candle_nf_fueled_batch_round_hi_def;
                  candle_cv_nf_fueled_batch_round_hi_def;
                  candle_cv_nf_fueled_polynomial_round_hi_correct;
                  cexp_fst_def; cexp_snd_def; FST; SND]);;

let candle_cv_nf_fueled_batch_compute_eqs =
  map SPEC_ALL [candle_cv_nf_fueled_batch_round_hi_compute] @
  candle_cv_nf_fueled_polynomial_compute_eqs;;

end;;
