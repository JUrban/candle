needs "candle/compute.ml";;
needs "candle/cv_compute_linear_combination_sparse_verdict.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_sparse_verdict;;

let candle_cv_lc_sparse_test_rows =
 `[(2,([(0,(1,0));(3,(0,2))],(5,0)));
   (3,([(0,(0,2));(3,(0,1))],(0,4)))]`;;
let candle_cv_lc_sparse_test_acc =
 `(([]:(num#(num#num))list),(0,0))`;;
let candle_cv_lc_sparse_test_expected =
 `([(0,(2,6));(3,(0,7))],(10,12))`;;

let candle_cv_lc_sparse_test_acc_rep =
  REWRITE_CONV[candle_cv_lc_sparse_acc_def;
               candle_cv_lc_sparse_vec_def;
               candle_cv_lc_sparse_entry_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_sparse_acc`,candle_cv_lc_sparse_test_acc));;
let candle_cv_lc_sparse_test_rows_rep =
  REWRITE_CONV[candle_cv_lc_sparse_rows_def;
               candle_cv_lc_sparse_row_def;
               candle_cv_lc_sparse_acc_def;
               candle_cv_lc_sparse_vec_def;
               candle_cv_lc_sparse_entry_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_sparse_rows`,candle_cv_lc_sparse_test_rows));;
let candle_cv_lc_sparse_test_tm =
  mk_comb
    (mk_comb
      (`candle_cv_lc_sparse_fold`,
       rand (concl candle_cv_lc_sparse_test_acc_rep)),
     rand (concl candle_cv_lc_sparse_test_rows_rep));;
let candle_cv_lc_sparse_test_compute =
  compute candle_cv_lc_sparse_compute_eqs candle_cv_lc_sparse_test_tm;;
let candle_cv_lc_sparse_test_expected_rep =
  REWRITE_CONV[candle_cv_lc_sparse_acc_def;
               candle_cv_lc_sparse_vec_def;
               candle_cv_lc_sparse_entry_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_sparse_acc`,candle_cv_lc_sparse_test_expected));;
let candle_cv_lc_sparse_test_correct =
  SPECL [candle_cv_lc_sparse_test_rows;candle_cv_lc_sparse_test_acc]
    candle_cv_lc_sparse_fold_correct;;
if hyp candle_cv_lc_sparse_test_compute <> [] ||
   hyp candle_cv_lc_sparse_test_correct <> [] ||
   not (aconv
     (rand (concl candle_cv_lc_sparse_test_compute))
     (rand (concl candle_cv_lc_sparse_test_expected_rep))) then
  failwith "sparse fold representation mismatch";;

let candle_cv_lc_sparse_cancel_rows =
 `[(2,([(0,(1,0));(3,(0,2))],(0,0)));
   (1,([(0,(0,2));(3,(4,0))],(0,1)))]`;;
let candle_cv_lc_sparse_cancel_rows_rep =
  REWRITE_CONV[candle_cv_lc_sparse_rows_def;
               candle_cv_lc_sparse_row_def;
               candle_cv_lc_sparse_acc_def;
               candle_cv_lc_sparse_vec_def;
               candle_cv_lc_sparse_entry_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_sparse_rows`,candle_cv_lc_sparse_cancel_rows));;
let candle_cv_lc_sparse_verdict_tm =
  mk_comb
    (mk_comb
      (`candle_cv_lc_sparse_fold_verdict`,
       rand (concl candle_cv_lc_sparse_test_acc_rep)),
     rand (concl candle_cv_lc_sparse_cancel_rows_rep));;
let candle_cv_lc_sparse_verdict_compute =
  compute candle_cv_lc_sparse_compute_eqs candle_cv_lc_sparse_verdict_tm;;
if hyp candle_cv_lc_sparse_verdict_compute <> [] ||
   not (aconv (rand (concl candle_cv_lc_sparse_verdict_compute))
              `Cexp_num 1`) then
  failwith "sparse one-shot verdict mismatch";;
let candle_cv_lc_sparse_verdict_correct =
  SPECL [candle_cv_lc_sparse_cancel_rows;candle_cv_lc_sparse_test_acc]
    candle_cv_lc_sparse_fold_verdict_correct;;
if hyp candle_cv_lc_sparse_verdict_correct <> [] then
  failwith "sparse verdict correctness has assumptions";;

print_endline "CANDLE_CV_LINEAR_COMBINATION_SPARSE_VERDICT_OK";;
