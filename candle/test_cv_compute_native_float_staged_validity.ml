needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_staged_validity.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;
open Candle_cv_native_float_staged_fold;;
open Candle_cv_native_float_staged_polynomial;;
open Candle_cv_native_float_staged_validity;;

let candle_nf_staged_validity_test_jobs =
 `CONS
    ((CONS ([0;0;0;0],(2,1))
       (CONS ([0;0;0;0],(3,2)) ([]:(num list#(num#num))list))),
     ([0;0;0;0],[0;0;0]))
    (CONS
      ((CONS ([0;0;0;0],(4,2)) ([]:(num list#(num#num))list)),
       ([0;0;0;0],[0]))
      ([]:(((num list#(num#num))list)#(num list#num list))list))`;;

let candle_nf_staged_validity_test_rep =
  REWRITE_CONV[candle_nf_staged_polynomial_jobs_def;
               candle_nf_staged_polynomial_job_def;
               candle_nf_staged_product_steps_def;
               candle_nf_staged_product_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_polynomial_jobs`,
      candle_nf_staged_validity_test_jobs));;

let candle_nf_staged_validity_test_compute =
  compute candle_cv_nf_staged_validity_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_polynomial_valid`,
       [`Cexp_num 10`; `Cexp_num 0`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_validity_test_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 0)`]));;

let candle_nf_staged_validity_test_correct =
  SPECL
    [candle_nf_staged_validity_test_jobs; `10`; `0`; `1000`; `(0,0)`]
    candle_cv_nf_staged_polynomial_valid_correct;;

let candle_nf_staged_validity_test_bad_jobs =
 `CONS
    ((CONS ([],(2,0)) ([]:(num list#(num#num))list)),([],[]))
    ([]:(((num list#(num#num))list)#(num list#num list))list)`;;

let candle_nf_staged_validity_test_bad_rep =
  REWRITE_CONV[candle_nf_staged_polynomial_jobs_def;
               candle_nf_staged_polynomial_job_def;
               candle_nf_staged_product_steps_def;
               candle_nf_staged_product_step_def;
               candle_nf_fuel_def; candle_nf_pair_def; FST; SND]
    (mk_comb (`candle_nf_staged_polynomial_jobs`,
      candle_nf_staged_validity_test_bad_jobs));;

let candle_nf_staged_validity_test_bad_compute =
  compute candle_cv_nf_staged_validity_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_staged_polynomial_valid`,
       [`Cexp_num 10`; `Cexp_num 1`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_validity_test_bad_rep);
        `Cexp_pair (Cexp_num 0) (Cexp_num 1)`]));;

if hyp candle_nf_staged_validity_test_compute <> [] ||
   hyp candle_nf_staged_validity_test_correct <> [] ||
   hyp candle_nf_staged_validity_test_bad_compute <> [] then
  failwith "staged validity theorem has assumptions";;

if rand (concl candle_nf_staged_validity_test_compute) <> `Cexp_num 1` ||
   rand (concl candle_nf_staged_validity_test_bad_compute) <> `Cexp_num 0` then
  failwith "staged validity result mismatch";;

print_endline "CANDLE_CV_NATIVE_FLOAT_STAGED_VALIDITY_OK";;
