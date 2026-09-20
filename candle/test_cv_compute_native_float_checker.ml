needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_checker.ml";;
needs "candle/test_cv_compute_native_float_batch.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_polynomial;;
open Candle_cv_native_float_batch;;
open Candle_cv_native_float_checker;;

let candle_nf_checker_test_bounds =
  `[1000000000000000000000000000000;
    1000000000000000000000000000000;
    1000000000000000000000000000000]`;;

let candle_nf_checker_test_bounds_rep =
  REWRITE_CONV[candle_nf_num_list_def]
    (mk_comb (`candle_nf_num_list`,candle_nf_checker_test_bounds));;

let candle_nf_checker_test_compute =
  compute candle_cv_nf_fueled_batch_checker_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_fueled_batch_check_hi`,
       [`Cexp_num 16`;
        rand (concl candle_nf_checker_test_bounds_rep);
        rand (concl candle_nf_batch_test_jobs_rep)]));;

if not (aconv (rand (concl candle_nf_checker_test_compute)) `Cexp_num 1`) then
  failwith "single-verdict native-float checker rejected valid batch";;

let candle_nf_checker_test_correct =
  SPECL
    [candle_nf_checker_test_bounds;candle_nf_batch_test_jobs;`16`]
    candle_cv_nf_fueled_batch_check_hi_correct;;

let candle_nf_checker_test_correct =
  PURE_REWRITE_RULE
    [candle_nf_checker_test_bounds_rep;candle_nf_batch_test_jobs_rep]
    candle_nf_checker_test_correct;;

let candle_nf_checker_test_encoded_true =
  REWRITE_RULE[injectivity "cval"]
    (TRANS (SYM candle_nf_checker_test_compute)
      candle_nf_checker_test_correct);;

let candle_nf_checker_one_true = prove
 (`!p. 1 = (if p then SUC 0 else 0) ==> p`,
  BOOL_CASES_TAC `p:bool` THEN REWRITE_TAC[] THEN ARITH_TAC);;

let candle_nf_checker_test_true =
  let predicate,_ =
    dest_cond (rand (concl candle_nf_checker_test_encoded_true)) in
  MATCH_MP (SPEC predicate candle_nf_checker_one_true)
    candle_nf_checker_test_encoded_true;;

let candle_nf_checker_test_sound =
  SPECL
    [candle_nf_batch_test_sources;candle_nf_batch_test_jobs;
     candle_nf_checker_test_bounds;`16`]
    candle_nf_fueled_batch_check_hi_sound;;

let candle_nf_checker_test_sound =
  MP candle_nf_checker_test_sound
    (CONJ candle_nf_batch_test_alignment candle_nf_checker_test_true);;

let candle_nf_checker_test_sound_items =
  REWRITE_RULE[candle_nf_batch_threshold_upper_def]
    candle_nf_checker_test_sound;;

if hyp candle_nf_checker_test_compute <> [] ||
   hyp candle_nf_checker_test_sound <> [] then
  failwith "single-verdict native-float checker theorem has assumptions";;

if length (CONJUNCTS candle_nf_checker_test_sound_items) <> 3 then
  failwith "single-verdict native-float checker theorem has wrong arity";;

print_endline "CANDLE_CV_NATIVE_FLOAT_CHECKER_OK";;
