needs "candle/cv_compute_exact_interval_recenter.ml";;

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_interval_recenter;;

let candle_q_recenter_test_variables = [`x:real`];;
let candle_q_recenter_test_centers = [`&1:real`];;
let candle_q_recenter_test_intervals =
 `([(((0,1),9),((1,0),9))]:
   (((num#num)#num)#((num#num)#num))list)`;;
let candle_q_recenter_test_expression = `x * x - &2 * x:real`;;

let candle_q_recenter_test_environment_imp = prove
 (`&9 / &10 <= x /\ x <= &11 / &10
   ==> candle_q_stack_contains
         ([(((0,1),9),((1,0),9))]:
          (((num#num)#num)#((num#num)#num))list)
         [x - &1]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def;candle_q_real_def;
              candle_q_den_def;candle_lc_zreal_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let candle_q_recenter_test_environment =
  UNDISCH candle_q_recenter_test_environment_imp;;

let candle_q_recenter_test_offsets,candle_q_recenter_test_normalized,
    candle_q_recenter_test_eq,candle_q_recenter_test_result,
    candle_q_recenter_test_program,candle_q_recenter_test_compute,
    candle_q_recenter_test_sound =
  candle_q_prove_recentered_interval_expression
    candle_q_recenter_test_variables candle_q_recenter_test_centers
    candle_q_recenter_test_intervals candle_q_recenter_test_environment
    candle_q_recenter_test_expression;;

let candle_q_recenter_test_expected =
 `(((((0,1),0),((1,100),99)):
     ((num#num)#num)#((num#num)#num)))`;;

if not (aconv candle_q_recenter_test_result candle_q_recenter_test_expected) then
  failwith "recentered exact interval result mismatch";;

if hyp candle_q_recenter_test_eq <> [] ||
   hyp candle_q_recenter_test_compute <> [] ||
   length (hyp candle_q_recenter_test_sound) <> 1
then failwith "recentered theorem assumptions mismatch";;

if length (dest_list candle_q_recenter_test_program) <> 4 then
  failwith "recentered program instruction count mismatch";;

print_endline "CANDLE_CV_EXACT_INTERVAL_RECENTER_OK";;
