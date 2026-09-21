needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_staged_polynomial.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;
open Candle_cv_native_float_staged_polynomial;;

let candle_nf_staged_polynomial_test_jobs =
 `CONS
    ((CONS ([0;0;0;0],(2,1))
       (CONS ([0;0;0;0],(3,2)) ([]:(num list#(num#num))list))),
     ([0;0;0;0],[0;0;0]))
    (CONS
      ((CONS ([0;0;0;0],(4,2)) ([]:(num list#(num#num))list)),
       ([0;0;0;0],[0]))
      ([]:(((num list#(num#num))list)#(num list#num list))list))`;;

let candle_nf_staged_polynomial_test_rep =
  REWRITE_CONV[candle_nf_staged_polynomial_jobs_def;
               candle_nf_staged_polynomial_job_def;
               candle_nf_staged_product_steps_def;
               candle_nf_staged_product_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_polynomial_jobs`,
      candle_nf_staged_polynomial_test_jobs));;

let candle_nf_staged_polynomial_test_compute =
  compute candle_cv_nf_staged_polynomial_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_polynomial`,
       [`Cexp_num 10`; `Cexp_num 0`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_polynomial_test_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 0)`]));;

let candle_nf_staged_polynomial_test_correct =
  SPECL
    [candle_nf_staged_polynomial_test_jobs; `10`; `0`; `1000`; `(0,0)`]
    candle_cv_nf_staged_polynomial_correct;;

let candle_nf_staged_polynomial_test_product1 =
  prove
   (`candle_nf_staged_product 10 0 1000
      [([0;0;0;0],(2,1));([0;0;0;0],(3,2))] (1,0) = (6,3)`,
    REWRITE_TAC[candle_nf_staged_product_def;
                candle_nf_scaled_mul_round_hi_def;
                candle_nf_round_hi_def; FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_polynomial_test_product2 =
  prove
   (`candle_nf_staged_product 10 0 1000
      [([0;0;0;0],(4,2))] (1,0) = (4,2)`,
    REWRITE_TAC[candle_nf_staged_product_def;
                candle_nf_scaled_mul_round_hi_def;
                candle_nf_round_hi_def; FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_polynomial_test_add1 =
  prove
   (`candle_nf_add_round_hi 10 1000 [0;0;0;0] [0;0;0]
      (0,0) (6,3) = (600,1)`,
    REWRITE_TAC[candle_nf_add_round_hi_def; candle_nf_add_raw_def;
                candle_nf_power_fuel_def; candle_nf_round_hi_def;
                FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_polynomial_test_valid =
  prove
   (`candle_nf_staged_polynomial_valid 10 0 1000
      [([([0;0;0;0],(2,1));([0;0;0;0],(3,2))],
        ([0;0;0;0],[0;0;0]));
       ([([0;0;0;0],(4,2))],([0;0;0;0],[0]))]
      (0,0)`,
    REWRITE_TAC[candle_nf_staged_polynomial_valid_def;
                candle_nf_staged_polynomial_test_product1;
                candle_nf_staged_polynomial_test_product2;
                candle_nf_staged_polynomial_test_add1;
                candle_nf_staged_product_valid_def;
                candle_nf_scaled_mul_round_hi_def;
                candle_nf_add_power_complete_def;
                candle_nf_add_round_hi_def; candle_nf_add_raw_def;
                candle_nf_power_fuel_def; candle_nf_round_hi_def;
                LENGTH; FST; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_polynomial_test_sound =
  MP
    (SPECL
      [candle_nf_staged_polynomial_test_jobs; `10`; `0`; `1000`; `(0,0)`]
      candle_nf_staged_polynomial_sound)
    (CONJ (EQT_ELIM (NUM_REDUCE_CONV `~(10 = 0)`))
      candle_nf_staged_polynomial_test_valid);;

if hyp candle_nf_staged_polynomial_test_compute <> [] ||
   hyp candle_nf_staged_polynomial_test_correct <> [] ||
   hyp candle_nf_staged_polynomial_test_sound <> [] then
  failwith "staged polynomial theorem has assumptions";;

if rand (concl candle_nf_staged_polynomial_test_compute) <>
   `Cexp_pair (Cexp_num 640) (Cexp_num 1)` then
  failwith "staged polynomial result mismatch";;

print_endline "CANDLE_CV_NATIVE_FLOAT_STAGED_POLYNOMIAL_OK";;
