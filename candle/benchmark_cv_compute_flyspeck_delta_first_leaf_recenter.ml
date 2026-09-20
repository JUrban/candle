(* ========================================================================== *)
(* Recentered exact-reflection profile for Flyspeck nonlinear case 7853.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  REAL_POLY_CONV selects a midpoint-centered    *)
(* polynomial, a kernel ring theorem authenticates it against delta_x * -1,  *)
(* and the reflected interval program evaluates only that authenticated form. *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_flyspeck_delta_first_leaf.ml";;
needs "candle/cv_compute_exact_interval_recenter.ml";;

open Candle_cv_exact_interval_recenter;;

let candle_q_flyspeck_delta_first_leaf_centers =
  [term_of_rat
    (Num.num_of_string "585677616661" //
     Num.num_of_string "125000000000");
   term_of_rat (Num.num_of_int 6469 // Num.num_of_int 1250);
   term_of_rat (Num.num_of_int 6469 // Num.num_of_int 1250);
   term_of_rat (Num.num_of_int 2385457 // Num.num_of_int 250000);
   `&4:real`;
   term_of_rat (Num.num_of_int 6469 // Num.num_of_int 1250)];;

let candle_q_flyspeck_delta_first_leaf_offset_intervals =
  mk_list
    ([candle_q_flyspeck_delta_interval
        (-85677616661) 125000000000 85677616661 125000000000;
      candle_q_flyspeck_delta_interval (-1469) 1250 1469 1250;
      candle_q_flyspeck_delta_interval (-1469) 1250 1469 1250;
      candle_q_flyspeck_delta_interval (-7527) 15625 7527 15625;
      candle_q_flyspeck_delta_interval 0 1 0 1;
      candle_q_flyspeck_delta_interval (-1469) 1250 1469 1250],
     candle_q_interval_type);;

let candle_q_flyspeck_delta_first_leaf_offset_environment_imp = prove
 (`&4 <= x1 /\ x1 <= &335677616661 / &62500000000 /\
   &4 <= x2 /\ x2 <= &3969 / &625 /\
   &4 <= x3 /\ x3 <= &3969 / &625 /\
   &90601 / &10000 <= x4 /\ x4 <= &2505889 / &250000 /\
   &4 <= x5 /\ x5 <= &4 /\
   &4 <= x6 /\ x6 <= &3969 / &625
   ==> candle_q_stack_contains
         ([(((0,85677616661),124999999999),
            ((85677616661,0),124999999999));
           (((0,1469),1249),((1469,0),1249));
           (((0,1469),1249),((1469,0),1249));
           (((0,7527),15624),((7527,0),15624));
           (((0,0),0),((0,0),0));
           (((0,1469),1249),((1469,0),1249))]:
          (((num#num)#num)#((num#num)#num))list)
         [x1 - &585677616661 / &125000000000;
          x2 - &6469 / &1250;
          x3 - &6469 / &1250;
          x4 - &2385457 / &250000;
          x5 - &4;
          x6 - &6469 / &1250]`,
  REWRITE_TAC[candle_q_stack_contains_def;
              candle_q_interval_contains_def;candle_q_real_def;
              candle_q_den_def;candle_lc_zreal_def] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let candle_q_flyspeck_delta_first_leaf_offset_environment =
  UNDISCH candle_q_flyspeck_delta_first_leaf_offset_environment_imp;;

print_endline
  "CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF_RECENTER stage=normalize event=begin";;

let candle_q_flyspeck_delta_first_leaf_offsets,
    candle_q_flyspeck_delta_first_leaf_normalized,
    candle_q_flyspeck_delta_first_leaf_recenter_eq,
    candle_q_flyspeck_delta_first_leaf_recenter_result,
    candle_q_flyspeck_delta_first_leaf_recenter_program,
    candle_q_flyspeck_delta_first_leaf_recenter_compute_th,
    candle_q_flyspeck_delta_first_leaf_recenter_sound_th =
  candle_q_prove_recentered_interval_expression
    candle_q_flyspeck_delta_variables
    candle_q_flyspeck_delta_first_leaf_centers
    candle_q_flyspeck_delta_first_leaf_offset_intervals
    candle_q_flyspeck_delta_first_leaf_offset_environment
    candle_q_flyspeck_delta_expression;;

print_endline
  ("CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF_RECENTER stage=normalize event=end instructions=" ^
   string_of_int
     (length (dest_list candle_q_flyspeck_delta_first_leaf_recenter_program)));;

let candle_q_flyspeck_delta_first_leaf_recenter_lo,
    candle_q_flyspeck_delta_first_leaf_recenter_hi =
  dest_pair candle_q_flyspeck_delta_first_leaf_recenter_result;;
let candle_q_flyspeck_delta_first_leaf_recenter_lo_z,
    candle_q_flyspeck_delta_first_leaf_recenter_lo_d =
  dest_pair candle_q_flyspeck_delta_first_leaf_recenter_lo;;
let candle_q_flyspeck_delta_first_leaf_recenter_hi_z,
    candle_q_flyspeck_delta_first_leaf_recenter_hi_d =
  dest_pair candle_q_flyspeck_delta_first_leaf_recenter_hi;;
let candle_q_flyspeck_delta_first_leaf_recenter_lo_p,
    candle_q_flyspeck_delta_first_leaf_recenter_lo_n =
  dest_pair candle_q_flyspeck_delta_first_leaf_recenter_lo_z;;
let candle_q_flyspeck_delta_first_leaf_recenter_hi_p,
    candle_q_flyspeck_delta_first_leaf_recenter_hi_n =
  dest_pair candle_q_flyspeck_delta_first_leaf_recenter_hi_z;;

print_endline
  (String.concat " "
    ["CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF_RECENTER stage=compute event=end";
     candle_q_flyspeck_delta_stat "lo_positive_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_lo_p;
     candle_q_flyspeck_delta_stat "lo_negative_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_lo_n;
     candle_q_flyspeck_delta_stat "lo_denominator_predecessor_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_lo_d;
     candle_q_flyspeck_delta_stat "hi_positive_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_hi_p;
     candle_q_flyspeck_delta_stat "hi_negative_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_hi_n;
     candle_q_flyspeck_delta_stat "hi_denominator_predecessor_bits"
       candle_q_flyspeck_delta_first_leaf_recenter_hi_d]);;

if hyp candle_q_flyspeck_delta_first_leaf_recenter_eq <> [] ||
   hyp candle_q_flyspeck_delta_first_leaf_recenter_compute_th <> [] ||
   length (hyp candle_q_flyspeck_delta_first_leaf_recenter_sound_th) <> 1
then failwith "Flyspeck recentered delta theorem assumptions mismatch";;

print_endline "CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF_RECENTER_OK";;
