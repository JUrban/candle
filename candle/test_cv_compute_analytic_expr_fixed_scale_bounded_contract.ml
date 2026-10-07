needs "candle/cv_compute_analytic_expr_fixed_scale_bounded_contract.ml";;

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_bounded_contract;;

let candle_cv_fs_bounded_test_compute tm =
  candle_q_dim_analytic_jet_compute
    (union candle_cv_fs_bounded_contract_compute_eqs
      candle_cv_fs_compute_eqs) tm;;

let candle_cv_fs_bounded_test_success =
  candle_cv_fs_bounded_test_compute
    `candle_cv_fs_bounded_checked (Cexp_num 8)
      (Cexp_pair (Cexp_num 7) (Cexp_num 0))`;;

let candle_cv_fs_bounded_test_overflow =
  candle_cv_fs_bounded_test_compute
    `candle_cv_fs_bounded_checked (Cexp_num 8)
      (Cexp_pair (Cexp_num 8) (Cexp_num 0))`;;

let candle_cv_fs_bounded_test_fallback =
  candle_cv_fs_bounded_test_compute
    `candle_cv_fs_bounded_with_fallback (Cexp_num 8)
      (Cexp_pair (Cexp_num 8) (Cexp_num 0))`;;

if hyp candle_cv_fs_bounded_test_success <> [] ||
   hyp candle_cv_fs_bounded_test_overflow <> [] ||
   hyp candle_cv_fs_bounded_test_fallback <> [] ||
   hyp candle_cv_fs_bounded_with_fallback_exact <> [] ||
   hyp candle_cv_fs_bounded_add_or_exact_correct <> [] ||
   hyp candle_cv_fs_bounded_mul_or_exact_correct <> [] ||
   not
     (aconv (rand (concl candle_cv_fs_bounded_test_success))
       `Cexp_pair (Cexp_num 1)
         (Cexp_pair (Cexp_num 7) (Cexp_num 0))`) ||
   not
     (aconv (rand (concl candle_cv_fs_bounded_test_overflow))
       `Cexp_pair (Cexp_num 0)
         (Cexp_pair (Cexp_num 0) (Cexp_num 0))`) ||
   not
     (aconv (rand (concl candle_cv_fs_bounded_test_fallback))
       `Cexp_pair (Cexp_num 8) (Cexp_num 0)`) then
  failwith "bounded fixed-scale contract focused test failed";;

print_endline
  "CANDLE_CV_FS_BOUNDED_CONTRACT_TEST_OK DEVELOPMENT_NON_RELEASE";;
