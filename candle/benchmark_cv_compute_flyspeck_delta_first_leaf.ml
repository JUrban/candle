(* ========================================================================== *)
(* Exact-reflection profile for the first real case-7853 partition leaf.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The top-level Iarg_facet takes the left       *)
(* 7637/10000 fraction of coordinate zero.  break_case_exec.mk_case_list     *)
(* emits that facet as the first independent leaf.                           *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_flyspeck_delta.ml";;

let candle_q_flyspeck_delta_first_leaf_intervals =
  mk_list
    ([candle_q_flyspeck_delta_interval 4 1 335677616661 62500000000;
      candle_q_flyspeck_delta_interval 4 1 3969 625;
      candle_q_flyspeck_delta_interval 4 1 3969 625;
      candle_q_flyspeck_delta_interval 90601 10000 2505889 250000;
      candle_q_flyspeck_delta_interval 4 1 4 1;
      candle_q_flyspeck_delta_interval 4 1 3969 625],
     candle_q_interval_type);;

let candle_q_flyspeck_delta_first_leaf_environment_imp = prove
 (`&4 <= x1 /\ x1 <= &335677616661 / &62500000000 /\
   &4 <= x2 /\ x2 <= &3969 / &625 /\
   &4 <= x3 /\ x3 <= &3969 / &625 /\
   &90601 / &10000 <= x4 /\ x4 <= &2505889 / &250000 /\
   &4 <= x5 /\ x5 <= &4 /\
   &4 <= x6 /\ x6 <= &3969 / &625
   ==> candle_q_stack_contains
         ([(((4,0),0),((335677616661,0),62499999999));
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

let candle_q_flyspeck_delta_first_leaf_environment =
  UNDISCH candle_q_flyspeck_delta_first_leaf_environment_imp;;

print_endline "CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF stage=compute event=begin";;

let candle_q_flyspeck_delta_first_leaf_result,_,
    candle_q_flyspeck_delta_first_leaf_compute_th,
    candle_q_flyspeck_delta_first_leaf_sound_th =
  candle_q_prove_interval_expression
    candle_q_flyspeck_delta_variables
    candle_q_flyspeck_delta_first_leaf_intervals
    candle_q_flyspeck_delta_first_leaf_environment
    candle_q_flyspeck_delta_expression;;

let candle_q_flyspeck_delta_first_leaf_lo,
    candle_q_flyspeck_delta_first_leaf_hi =
  dest_pair candle_q_flyspeck_delta_first_leaf_result;;
let candle_q_flyspeck_delta_first_leaf_lo_z,
    candle_q_flyspeck_delta_first_leaf_lo_d =
  dest_pair candle_q_flyspeck_delta_first_leaf_lo;;
let candle_q_flyspeck_delta_first_leaf_hi_z,
    candle_q_flyspeck_delta_first_leaf_hi_d =
  dest_pair candle_q_flyspeck_delta_first_leaf_hi;;
let candle_q_flyspeck_delta_first_leaf_lo_p,
    candle_q_flyspeck_delta_first_leaf_lo_n =
  dest_pair candle_q_flyspeck_delta_first_leaf_lo_z;;
let candle_q_flyspeck_delta_first_leaf_hi_p,
    candle_q_flyspeck_delta_first_leaf_hi_n =
  dest_pair candle_q_flyspeck_delta_first_leaf_hi_z;;

print_endline
  (String.concat " "
    ["CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF stage=compute event=end";
     candle_q_flyspeck_delta_stat "lo_positive_bits"
       candle_q_flyspeck_delta_first_leaf_lo_p;
     candle_q_flyspeck_delta_stat "lo_negative_bits"
       candle_q_flyspeck_delta_first_leaf_lo_n;
     candle_q_flyspeck_delta_stat "lo_denominator_predecessor_bits"
       candle_q_flyspeck_delta_first_leaf_lo_d;
     candle_q_flyspeck_delta_stat "hi_positive_bits"
       candle_q_flyspeck_delta_first_leaf_hi_p;
     candle_q_flyspeck_delta_stat "hi_negative_bits"
       candle_q_flyspeck_delta_first_leaf_hi_n;
     candle_q_flyspeck_delta_stat "hi_denominator_predecessor_bits"
       candle_q_flyspeck_delta_first_leaf_hi_d]);;

if hyp candle_q_flyspeck_delta_first_leaf_compute_th <> [] ||
   length (hyp candle_q_flyspeck_delta_first_leaf_sound_th) <> 1
then failwith "Flyspeck delta first-leaf theorem assumptions mismatch";;

print_endline "CANDLE_CV_FLYSPECK_DELTA_FIRST_LEAF_OK";;
