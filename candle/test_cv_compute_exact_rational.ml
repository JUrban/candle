needs "candle/compute.ml";;
needs "candle/cv_compute_exact_rational.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_rational;;

let candle_cv_q_test_x = `((3,1),4):(num#num)#num`;;
let candle_cv_q_test_y = `((2,5),2):(num#num)#num`;;
let candle_cv_q_test_i =
 `(((3,1),4),((2,5),2)):
   ((num#num)#num)#((num#num)#num)`;;
let candle_cv_q_test_j =
 `(((2,5),2),((3,1),4)):
   ((num#num)#num)#((num#num)#num)`;;

let candle_cv_q_test_add_th =
  candle_q_add_conv candle_cv_q_test_x candle_cv_q_test_y;;
let candle_cv_q_test_mul_th =
  candle_q_mul_conv candle_cv_q_test_x candle_cv_q_test_y;;
let candle_cv_q_test_neg_th = candle_q_neg_conv candle_cv_q_test_x;;
let candle_cv_q_test_interval_add_th =
  candle_q_interval_add_conv candle_cv_q_test_i candle_cv_q_test_j;;
let candle_cv_q_test_interval_neg_th =
  candle_q_interval_neg_conv candle_cv_q_test_i;;

if hyp candle_cv_q_test_add_th <> [] ||
   not (aconv (concl candle_cv_q_test_add_th)
      `candle_q_add ((3,1),4) ((2,5),2) = ((19,28),14)`)
then failwith "ordinary rational-add theorem handoff mismatch";;

if hyp candle_cv_q_test_mul_th <> [] ||
   not (aconv (concl candle_cv_q_test_mul_th)
      `candle_q_mul ((3,1),4) ((2,5),2) = ((11,17),14)`)
then failwith "ordinary rational-mul theorem handoff mismatch";;

if hyp candle_cv_q_test_neg_th <> [] ||
   not (aconv (concl candle_cv_q_test_neg_th)
      `candle_q_neg ((3,1),4) = ((1,3),4)`)
then failwith "ordinary rational-neg theorem handoff mismatch";;

if hyp candle_cv_q_test_interval_add_th <> [] ||
   not (aconv (concl candle_cv_q_test_interval_add_th)
      `candle_q_interval_add
         (((3,1),4),((2,5),2))
         (((2,5),2),((3,1),4)) =
       (((19,28),14),((19,28),14))`)
then failwith "ordinary interval-add theorem handoff mismatch";;

if hyp candle_cv_q_test_interval_neg_th <> [] ||
   not (aconv (concl candle_cv_q_test_interval_neg_th)
      `candle_q_interval_neg (((3,1),4),((2,5),2)) =
       (((5,2),2),((1,3),4))`)
then failwith "ordinary interval-neg theorem handoff mismatch";;

if hyp candle_cv_q_interval_roundtrip <> [] ||
   hyp candle_cv_q_interval_add_correct <> [] ||
   hyp candle_cv_q_interval_neg_correct <> [] ||
   hyp candle_q_interval_add_sound <> [] ||
   hyp candle_q_interval_neg_sound <> []
then failwith "interval theorem has assumptions";;

print_endline "CANDLE_CV_EXACT_RATIONAL_OK";;
