needs "candle/compute.ml";;
needs "candle/cv_compute_linear_combination_core.ml";;
needs "candle/cv_compute_linear_combination.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination;;

let candle_cv_lc_test_rows =
 `[(3,([(2,0);(0,1)],(5,0)));
   (2,([(0,3);(4,0)],(0,7)));
   (5,([(1,1)],(2,9)))]:
   (num#((num#num)list#(num#num)))list`;;

let candle_cv_lc_test_acc =
 `([(0,0);(0,0)],(0,0)):(num#num)list#(num#num)`;;

let candle_cv_lc_test_acc_rep =
  REWRITE_CONV[candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_acc`,candle_cv_lc_test_acc));;

let candle_cv_lc_test_rows_rep =
  REWRITE_CONV[candle_cv_lc_rows_def; candle_cv_lc_row_def;
               candle_cv_lc_acc_def; candle_cv_lc_vec_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_lc_rows`,candle_cv_lc_test_rows));;

let candle_cv_lc_test_tm =
  mk_comb
    (mk_comb (`candle_cv_lc_fold`,rand (concl candle_cv_lc_test_acc_rep)),
     rand (concl candle_cv_lc_test_rows_rep));;

let candle_cv_lc_test_compute =
  compute candle_cv_lc_compute_eqs candle_cv_lc_test_tm;;

let candle_cv_lc_test_expected =
 `Cexp_pair
   (Cexp_pair (Cexp_pair (Cexp_num 11) (Cexp_num 11))
    (Cexp_pair (Cexp_pair (Cexp_num 8) (Cexp_num 3)) (Cexp_num 0)))
   (Cexp_pair (Cexp_num 25) (Cexp_num 59))`;;

if hyp candle_cv_lc_test_compute <> [] then
  failwith "linear-combination compute theorem has assumptions";;
if not (aconv (rand (concl candle_cv_lc_test_compute))
              candle_cv_lc_test_expected) then
  failwith "linear-combination compute result mismatch";;

let candle_cv_lc_test_correct =
  SPECL [candle_cv_lc_test_rows;candle_cv_lc_test_acc]
        candle_cv_lc_fold_correct;;

if hyp candle_cv_lc_test_correct <> [] then
  failwith "linear-combination representation theorem has assumptions";;

let candle_cv_lc_test_ordinary =
  candle_cv_lc_fold_conv candle_cv_lc_test_acc candle_cv_lc_test_rows;;

let candle_cv_lc_test_ordinary_expected =
 `candle_lc_fold
    ([(0,0);(0,0)],(0,0))
    [(3,([(2,0);(0,1)],(5,0)));
     (2,([(0,3);(4,0)],(0,7)));
     (5,([(1,1)],(2,9)))] =
   ([(11,11);(8,3)],(25,59))`;;

if hyp candle_cv_lc_test_ordinary <> [] then
  failwith "ordinary linear-combination theorem has assumptions";;
if not (aconv (concl candle_cv_lc_test_ordinary)
              candle_cv_lc_test_ordinary_expected) then
  failwith "ordinary linear-combination theorem interface mismatch";;

print_endline "CANDLE_CV_LINEAR_COMBINATION_CORE_OK";;
