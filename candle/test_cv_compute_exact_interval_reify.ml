needs "candle/cv_compute_exact_interval_reify.ml";;

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;

let candle_q_reify_test_x = `x:real`;;
let candle_q_reify_test_y = `y:real`;;
let candle_q_reify_test_z = `z:real`;;
let candle_q_reify_test_variables =
  [candle_q_reify_test_x;candle_q_reify_test_y;candle_q_reify_test_z];;

let candle_q_reify_test_intervals =
 `([(((1,0),0),((2,0),0));
    (((0,1),0),((1,0),0));
    (((2,0),0),((3,0),0))]:
   (((num#num)#num)#((num#num)#num))list)`;;

let candle_q_reify_test_expression =
 `((x - y) * (z + &3 / &2) + x pow 3):real`;;

let candle_q_reify_test_environment_imp = prove
 (`&1 <= x /\ x <= &2 /\ -- &1 <= y /\ y <= &1 /\
   &2 <= z /\ z <= &3
   ==> candle_q_stack_contains
         ([(((1,0),0),((2,0),0));
           (((0,1),0),((1,0),0));
           (((2,0),0),((3,0),0))]:
          (((num#num)#num)#((num#num)#num))list)
         [x;y;z]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let candle_q_reify_test_environment =
  UNDISCH candle_q_reify_test_environment_imp;;

let candle_q_reify_test_result,candle_q_reify_test_program,
    candle_q_reify_test_compute,candle_q_reify_test_sound =
  candle_q_prove_interval_expression
    candle_q_reify_test_variables candle_q_reify_test_intervals
    candle_q_reify_test_environment candle_q_reify_test_expression;;

let candle_q_reify_test_expected =
 `(((((9,7),1),((43,0),1)):
     ((num#num)#num)#((num#num)#num)))`;;

if not (aconv candle_q_reify_test_result candle_q_reify_test_expected) then
  failwith "exact interval reifier result mismatch";;

if hyp candle_q_reify_test_compute <> [] then
  failwith "exact interval reifier compute theorem has assumptions";;

if length (hyp candle_q_reify_test_sound) <> 1 ||
   not
     (aconv
       (concl candle_q_reify_test_sound)
       (list_mk_comb
         (`candle_q_interval_contains`,
          [candle_q_reify_test_expected;candle_q_reify_test_expression])))
then failwith "exact interval reifier sound theorem mismatch";;

let candle_q_reify_test_program_items =
  dest_list candle_q_reify_test_program;;

if length candle_q_reify_test_program_items <> 13 then
  failwith "exact interval reifier instruction count mismatch";;

let candle_q_reify_unsupported_division =
  try
    let _ = candle_q_reify_real_expression
      candle_q_reify_test_variables `x / y:real` in false
  with Failure _ -> true;;

if not candle_q_reify_unsupported_division then
  failwith "exact interval reifier accepted unsupported division";;

let candle_q_reify_unsupported_power =
  try
    let _ = candle_q_reify_real_expression
      candle_q_reify_test_variables `x pow 17:real` in false
  with Failure _ -> true;;

if not candle_q_reify_unsupported_power then
  failwith "exact interval reifier accepted oversized exponent";;

print_endline "CANDLE_CV_EXACT_INTERVAL_REIFY_OK";;
