needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_mul_core.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_mul_core;;

let candle_cv_q_mul_test_i =
 `(((2,5),2),((3,1),4)):
   ((num#num)#num)#((num#num)#num)`;;

let candle_cv_q_mul_test_i_rep =
  REWRITE_CONV[candle_cv_q_interval_def; candle_cv_q_def;
               candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval`,candle_cv_q_mul_test_i));;

let candle_cv_q_mul_test_th =
  compute candle_cv_q_interval_mul_compute_eqs
    (mk_comb
      (mk_comb (`candle_cv_q_interval_mul`,
        rand (concl candle_cv_q_mul_test_i_rep)),
       rand (concl candle_cv_q_mul_test_i_rep)));;

let candle_cv_q_mul_test_expected =
 `Cexp_pair
    (Cexp_pair (Cexp_pair (Cexp_num 11) (Cexp_num 17)) (Cexp_num 14))
    (Cexp_pair (Cexp_pair (Cexp_num 29) (Cexp_num 20)) (Cexp_num 8))`;;

if hyp candle_cv_q_mul_test_th <> [] ||
   not (aconv (rand (concl candle_cv_q_mul_test_th))
              candle_cv_q_mul_test_expected)
then failwith "exact interval multiplication compute mismatch";;

if hyp candle_real_interval_mul <> [] ||
   hyp candle_q_interval_mul_sound <> [] ||
   hyp candle_cv_q_interval_mul_correct <> []
then failwith "exact interval multiplication theorem has assumptions";;

print_endline "CANDLE_CV_EXACT_INTERVAL_MUL_CORE_OK";;
