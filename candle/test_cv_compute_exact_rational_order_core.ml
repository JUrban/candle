needs "candle/compute.ml";;
needs "candle/cv_compute_exact_rational_order_core.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_order_core;;

let candle_cv_q_order_test_x = `((3,1),4):(num#num)#num`;;
let candle_cv_q_order_test_y = `((2,5),2):(num#num)#num`;;

let candle_cv_q_order_test_x_rep =
  REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q`,candle_cv_q_order_test_x));;
let candle_cv_q_order_test_y_rep =
  REWRITE_CONV[candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q`,candle_cv_q_order_test_y));;

let candle_cv_q_order_compute op left right =
  compute candle_cv_q_order_compute_eqs
    (mk_comb
      (mk_comb (op,rand (concl left)),
       rand (concl right)));;

let candle_cv_q_order_test_xy =
  candle_cv_q_order_compute `candle_cv_q_le`
    candle_cv_q_order_test_x_rep candle_cv_q_order_test_y_rep;;
let candle_cv_q_order_test_yx =
  candle_cv_q_order_compute `candle_cv_q_le`
    candle_cv_q_order_test_y_rep candle_cv_q_order_test_x_rep;;
let candle_cv_q_order_test_min =
  candle_cv_q_order_compute `candle_cv_q_min`
    candle_cv_q_order_test_x_rep candle_cv_q_order_test_y_rep;;
let candle_cv_q_order_test_max =
  candle_cv_q_order_compute `candle_cv_q_max`
    candle_cv_q_order_test_x_rep candle_cv_q_order_test_y_rep;;

if hyp candle_cv_q_order_test_xy <> [] ||
   not (aconv (rand (concl candle_cv_q_order_test_xy)) `Cexp_num 0`)
then failwith "exact-rational x <= y mismatch";;
if hyp candle_cv_q_order_test_yx <> [] ||
   not (aconv (rand (concl candle_cv_q_order_test_yx)) `Cexp_num 1`)
then failwith "exact-rational y <= x mismatch";;
if hyp candle_cv_q_order_test_min <> [] ||
   not (aconv (rand (concl candle_cv_q_order_test_min))
      (rand (concl candle_cv_q_order_test_y_rep)))
then failwith "exact-rational minimum mismatch";;
if hyp candle_cv_q_order_test_max <> [] ||
   not (aconv (rand (concl candle_cv_q_order_test_max))
      (rand (concl candle_cv_q_order_test_x_rep)))
then failwith "exact-rational maximum mismatch";;

if hyp candle_q_le_real <> [] ||
   hyp candle_q_min_real <> [] ||
   hyp candle_q_max_real <> [] ||
   hyp candle_cv_q_le_correct <> [] ||
   hyp candle_cv_q_min_correct <> [] ||
   hyp candle_cv_q_max_correct <> []
then failwith "exact-rational order theorem has assumptions";;

print_endline "CANDLE_CV_EXACT_RATIONAL_ORDER_CORE_OK";;
