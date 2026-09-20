(* ========================================================================== *)
(* Focused exact-reflection profile for a real Flyspeck nonlinear polynomial. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The expression is the exact right-hand side  *)
(* of delta_x from text_formalization/general/sphere.hl, multiplied by -1 as *)
(* it occurs in the selected global nonlinear case 7853.  The six intervals *)
(* are that case's authenticated public bounds.                              *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_reify.ml";;

open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;

let candle_q_flyspeck_delta_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_q_flyspeck_delta_expression =
 `((x1*x4*(--x1 + x2 + x3 - x4 + x5 + x6) +
    x2*x5*(x1 - x2 + x3 + x4 - x5 + x6) +
    x3*x6*(x1 + x2 - x3 + x4 + x5 - x6) -
    x2*x3*x4 - x1*x3*x5 - x1*x2*x6 - x4*x5*x6) * -- &1):real`;;

let candle_q_flyspeck_delta_interval lo_n lo_d hi_n hi_d =
  mk_pair
    (candle_q_term
      (Num.num_of_int lo_n // Num.num_of_int lo_d),
     candle_q_term
      (Num.num_of_int hi_n // Num.num_of_int hi_d));;

let candle_q_flyspeck_delta_intervals =
  mk_list
    ([candle_q_flyspeck_delta_interval 4 1 36218753 6250000;
      candle_q_flyspeck_delta_interval 4 1 3969 625;
      candle_q_flyspeck_delta_interval 4 1 3969 625;
      candle_q_flyspeck_delta_interval 90601 10000 2505889 250000;
      candle_q_flyspeck_delta_interval 4 1 4 1;
      candle_q_flyspeck_delta_interval 4 1 3969 625],
     candle_q_interval_type);;

let candle_q_flyspeck_delta_environment_imp = prove
 (`&4 <= x1 /\ x1 <= &36218753 / &6250000 /\
   &4 <= x2 /\ x2 <= &3969 / &625 /\
   &4 <= x3 /\ x3 <= &3969 / &625 /\
   &90601 / &10000 <= x4 /\ x4 <= &2505889 / &250000 /\
   &4 <= x5 /\ x5 <= &4 /\
   &4 <= x6 /\ x6 <= &3969 / &625
   ==> candle_q_stack_contains
         ([(((4,0),0),((36218753,0),6249999));
           (((4,0),0),((3969,0),624));
           (((4,0),0),((3969,0),624));
           (((90601,0),9999),((2505889,0),249999));
           (((4,0),0),((4,0),0));
           (((4,0),0),((3969,0),624))]:
          (((num#num)#num)#((num#num)#num))list)
         [x1;x2;x3;x4;x5;x6]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def; candle_q_real_def;
              candle_q_den_def; candle_lc_zreal_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let candle_q_flyspeck_delta_environment =
  UNDISCH candle_q_flyspeck_delta_environment_imp;;

print_endline "CANDLE_CV_FLYSPECK_DELTA stage=reify event=begin";;

let candle_q_flyspeck_delta_program,candle_q_flyspeck_delta_real_th =
  candle_q_reify_real_expression
    candle_q_flyspeck_delta_variables candle_q_flyspeck_delta_expression;;

print_endline
  ("CANDLE_CV_FLYSPECK_DELTA stage=reify event=end instructions=" ^
   string_of_int (length (dest_list candle_q_flyspeck_delta_program)));;

print_endline "CANDLE_CV_FLYSPECK_DELTA stage=compute event=begin";;

let candle_q_flyspeck_delta_result,_,candle_q_flyspeck_delta_compute_th,
    candle_q_flyspeck_delta_sound_th =
  candle_q_prove_interval_expression
    candle_q_flyspeck_delta_variables candle_q_flyspeck_delta_intervals
    candle_q_flyspeck_delta_environment candle_q_flyspeck_delta_expression;;

let rec candle_q_flyspeck_delta_num_bits value count =
  if value =/ Num.num_of_int 0 then count
  else candle_q_flyspeck_delta_num_bits
    (Num.quo_num (Num.abs_num value) (Num.num_of_int 2)) (count + 1);;

let candle_q_flyspeck_delta_lo,candle_q_flyspeck_delta_hi =
  dest_pair candle_q_flyspeck_delta_result;;
let candle_q_flyspeck_delta_lo_z,candle_q_flyspeck_delta_lo_d =
  dest_pair candle_q_flyspeck_delta_lo;;
let candle_q_flyspeck_delta_hi_z,candle_q_flyspeck_delta_hi_d =
  dest_pair candle_q_flyspeck_delta_hi;;
let candle_q_flyspeck_delta_lo_p,candle_q_flyspeck_delta_lo_n =
  dest_pair candle_q_flyspeck_delta_lo_z;;
let candle_q_flyspeck_delta_hi_p,candle_q_flyspeck_delta_hi_n =
  dest_pair candle_q_flyspeck_delta_hi_z;;

let candle_q_flyspeck_delta_stat name tm =
  let value = dest_numeral tm in
  name ^ "=" ^
  string_of_int (candle_q_flyspeck_delta_num_bits value 0);;

print_endline
  (String.concat " "
    ["CANDLE_CV_FLYSPECK_DELTA stage=compute event=end";
     candle_q_flyspeck_delta_stat "lo_positive_bits"
       candle_q_flyspeck_delta_lo_p;
     candle_q_flyspeck_delta_stat "lo_negative_bits"
       candle_q_flyspeck_delta_lo_n;
     candle_q_flyspeck_delta_stat "lo_denominator_predecessor_bits"
       candle_q_flyspeck_delta_lo_d;
     candle_q_flyspeck_delta_stat "hi_positive_bits"
       candle_q_flyspeck_delta_hi_p;
     candle_q_flyspeck_delta_stat "hi_negative_bits"
       candle_q_flyspeck_delta_hi_n;
     candle_q_flyspeck_delta_stat "hi_denominator_predecessor_bits"
       candle_q_flyspeck_delta_hi_d]);;

if hyp candle_q_flyspeck_delta_real_th <> [] ||
   hyp candle_q_flyspeck_delta_compute_th <> [] ||
   length (hyp candle_q_flyspeck_delta_sound_th) <> 1
then failwith "Flyspeck delta profile theorem assumptions mismatch";;

print_endline "CANDLE_CV_FLYSPECK_DELTA_OK";;
