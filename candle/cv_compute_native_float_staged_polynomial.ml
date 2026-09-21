(* ========================================================================== *)
(* A proof-producing staged polynomial evaluator for nonnegative floats.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Each job first evaluates one product with an    *)
(* upward rounding after every multiplication, then adds that rounded term to *)
(* the accumulator with an authenticated exponent-alignment witness. The      *)
(* complete polynomial executes behind one Kernel.compute call.               *)
(* ========================================================================== *)

needs "candle/cv_compute_native_float_staged_fold.ml";;

module Candle_cv_native_float_staged_polynomial = struct

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;

(* A job is (product steps,(sum rounding fuel,sum alignment fuel)). *)
let candle_nf_staged_polynomial_def = define
 `(candle_nf_staged_polynomial radix scale limit
      ([]:(((num list#(num#num))list)#(num list#num list))list) acc = acc) /\
  (candle_nf_staged_polynomial radix scale limit (CONS h t) acc =
     candle_nf_staged_polynomial radix scale limit t
       (candle_nf_add_round_hi radix limit (FST (SND h)) (SND (SND h))
         acc
         (candle_nf_staged_product radix scale limit (FST h)
           (1,scale))))`;;

let candle_nf_staged_polynomial_valid_def = define
 `(candle_nf_staged_polynomial_valid radix scale limit
      ([]:(((num list#(num#num))list)#(num list#num list))list) acc <=> T) /\
  (candle_nf_staged_polynomial_valid radix scale limit (CONS h t) acc <=>
     candle_nf_staged_product_valid radix scale limit (FST h) (1,scale) /\
     candle_nf_add_power_complete (SND (SND h)) acc
       (candle_nf_staged_product radix scale limit (FST h) (1,scale)) /\
     candle_nf_staged_polynomial_valid radix scale limit t
       (candle_nf_add_round_hi radix limit (FST (SND h)) (SND (SND h))
         acc
         (candle_nf_staged_product radix scale limit (FST h)
           (1,scale))))`;;

let candle_nf_staged_polynomial_value_def = define
 `(candle_nf_staged_polynomial_value radix scale limit
      ([]:(((num list#(num#num))list)#(num list#num list))list) = 0) /\
  (candle_nf_staged_polynomial_value radix scale limit (CONS h t) =
     candle_nf_value radix
       (candle_nf_staged_product radix scale limit (FST h) (1,scale)) +
     candle_nf_staged_polynomial_value radix scale limit t)`;;

let candle_nf_staged_polynomial_sound = prove
 (`!jobs radix scale limit acc.
     ~(radix = 0) /\
     candle_nf_staged_polynomial_valid radix scale limit jobs acc
     ==> candle_nf_value radix acc +
           candle_nf_staged_polynomial_value radix scale limit jobs <=
         candle_nf_value radix
           (candle_nf_staged_polynomial radix scale limit jobs acc)`,
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_def;
                candle_nf_staged_polynomial_valid_def;
                candle_nf_staged_polynomial_value_def;
                ADD_CLAUSES; LE_REFL];
    FIRST_X_ASSUM (LABEL_TAC "IH") THEN
    REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_nf_staged_polynomial_def;
                candle_nf_staged_polynomial_valid_def;
                candle_nf_staged_polynomial_value_def] THEN
    STRIP_TAC THEN
    MP_TAC
      (MATCH_MP
        (SPECL
          [`radix:num`; `limit:num`;
           `FST (SND
             (h:((num list#(num#num))list)#(num list#num list)))`;
           `SND (SND
             (h:((num list#(num#num))list)#(num list#num list)))`;
           `acc:num#num`;
           `candle_nf_staged_product radix scale limit
             (FST (h:((num list#(num#num))list)#(num list#num list)))
             (1,scale)`]
          candle_nf_add_round_hi_sound)
        (CONJ
          (ASSUME `~(radix = 0)`)
          (ASSUME
            `candle_nf_add_power_complete
               (SND (SND
                 (h:((num list#(num#num))list)#(num list#num list))))
               (acc:num#num)
               (candle_nf_staged_product radix scale limit (FST h)
                 (1,scale))`))) THEN
    DISCH_THEN (LABEL_TAC "HEAD") THEN
    USE_THEN "IH" (fun ih ->
      MP_TAC
       (MATCH_MP
         (SPECL
           [`radix:num`; `scale:num`; `limit:num`;
            `candle_nf_add_round_hi radix limit
               (FST (SND
                 (h:((num list#(num#num))list)#(num list#num list))))
               (SND (SND h)) (acc:num#num)
               (candle_nf_staged_product radix scale limit (FST h)
                 (1,scale))`]
           ih)
         (CONJ
           (ASSUME `~(radix = 0)`)
           (ASSUME
             `candle_nf_staged_polynomial_valid radix scale limit t
                (candle_nf_add_round_hi radix limit
                  (FST (SND
                    (h:((num list#(num#num))list)#(num list#num list))))
                  (SND (SND h)) (acc:num#num)
                  (candle_nf_staged_product radix scale limit (FST h)
                    (1,scale)))`)))) THEN
    DISCH_THEN (LABEL_TAC "TAIL") THEN
    USE_THEN "HEAD" (fun head ->
      USE_THEN "TAIL" (fun tail ->
        let inst =
          SPECL
            [`candle_nf_value radix (acc:num#num)`;
             `candle_nf_value radix
                (candle_nf_staged_product radix scale limit
                  (FST
                    (h:((num list#(num#num))list)#(num list#num list)))
                  (1,scale))`;
             `candle_nf_value radix
                (candle_nf_add_round_hi radix limit
                  (FST (SND
                    (h:((num list#(num#num))list)#(num list#num list))))
                  (SND (SND h)) acc
                  (candle_nf_staged_product radix scale limit (FST h)
                    (1,scale)))`;
             `candle_nf_staged_polynomial_value radix scale limit
                (t:(((num list#(num#num))list)#
                    (num list#num list))list)`;
             `candle_nf_value radix
                (candle_nf_staged_polynomial radix scale limit t
                  (candle_nf_add_round_hi radix limit
                    (FST (SND
                      (h:((num list#(num#num))list)#(num list#num list))))
                    (SND (SND h)) acc
                    (candle_nf_staged_product radix scale limit (FST h)
                      (1,scale))))`]
            candle_nf_staged_sum_bound_step in
        MATCH_ACCEPT_TAC (MATCH_MP inst (CONJ head tail))))]);;

let candle_nf_staged_polynomial_job_def = new_definition
 `candle_nf_staged_polynomial_job
      (job:((num list#(num#num))list)#(num list#num list)) =
    Cexp_pair (candle_nf_staged_product_steps (FST job))
      (Cexp_pair (candle_nf_fuel (FST (SND job)))
        (candle_nf_fuel (SND (SND job))))`;;

let candle_nf_staged_polynomial_jobs_def = define
 `(candle_nf_staged_polynomial_jobs
      ([]:(((num list#(num#num))list)#(num list#num list))list) =
     Cexp_num 0) /\
  (candle_nf_staged_polynomial_jobs (CONS h t) =
     Cexp_pair (candle_nf_staged_polynomial_job h)
       (candle_nf_staged_polynomial_jobs t))`;;

let candle_cv_nf_staged_polynomial_def = define
 `(candle_cv_nf_staged_polynomial radix scale limit (Cexp_num z) acc = acc) /\
  (candle_cv_nf_staged_polynomial radix scale limit (Cexp_pair h t) acc =
     candle_cv_nf_staged_polynomial radix scale limit t
       (candle_cv_nf_add_round_hi radix limit
         (Cexp_fst (Cexp_snd h)) (Cexp_snd (Cexp_snd h)) acc
         (candle_cv_nf_staged_product radix scale limit (Cexp_fst h)
           (Cexp_pair (Cexp_num 1) scale))))`;;

let candle_cv_nf_staged_polynomial_compute = prove
 (`!radix scale limit jobs acc.
     candle_cv_nf_staged_polynomial radix scale limit jobs acc =
     Cexp_if (Cexp_ispair jobs)
       (candle_cv_nf_staged_polynomial radix scale limit (Cexp_snd jobs)
         (candle_cv_nf_add_round_hi radix limit
           (Cexp_fst (Cexp_snd (Cexp_fst jobs)))
           (Cexp_snd (Cexp_snd (Cexp_fst jobs))) acc
           (candle_cv_nf_staged_product radix scale limit
             (Cexp_fst (Cexp_fst jobs))
             (Cexp_pair (Cexp_num 1) scale))))
       acc`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_nf_staged_polynomial_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_nf_staged_polynomial_one_rep = prove
 (`!scale.
     Cexp_pair (Cexp_num 1) (Cexp_num scale) =
     candle_nf_pair (1,scale)`,
  REWRITE_TAC[candle_nf_pair_def; FST; SND]);;

let candle_cv_nf_staged_polynomial_correct = prove
 (`!jobs radix scale limit acc.
     candle_cv_nf_staged_polynomial
       (Cexp_num radix) (Cexp_num scale) (Cexp_num limit)
       (candle_nf_staged_polynomial_jobs jobs) (candle_nf_pair acc) =
     candle_nf_pair
       (candle_nf_staged_polynomial radix scale limit jobs acc)`,
  LIST_INDUCT_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[candle_nf_staged_polynomial_jobs_def;
                  candle_nf_staged_polynomial_job_def;
                  candle_nf_staged_polynomial_def;
                  candle_cv_nf_staged_polynomial_def;
                  cexp_fst_def; cexp_snd_def;
                  candle_nf_staged_polynomial_one_rep;
                  candle_cv_nf_staged_product_correct;
                  candle_cv_nf_add_round_hi_correct]);;

let candle_cv_nf_staged_polynomial_compute_eqs =
  map SPEC_ALL [candle_cv_nf_staged_polynomial_compute] @
  candle_cv_nf_staged_fold_compute_eqs;;

end;;
