(* ========================================================================== *)
(* Focused tests for checked adaptive exact-rational normalization.           *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_rational_normalize.ml";;

open Candle_cv_exact_rational_normalize;;

let candle_adaptive_gcd_compute_eqs =
  Candle_cv_exact_rational_core.candle_cv_q_compute_eqs @
  candle_cv_q_normalized_compute_eqs;;

let candle_adaptive_gcd_fibonacci_pair steps =
  let rec loop n a b =
    if n = 0 then a,b else loop (n - 1) (Num.add_num a b) a in
  loop steps (Num.num_of_int 1) (Num.num_of_int 1);;

let candle_adaptive_gcd_a,candle_adaptive_gcd_b =
  candle_adaptive_gcd_fibonacci_pair 140;;

let candle_adaptive_gcd_a_tm = mk_numeral candle_adaptive_gcd_a
and candle_adaptive_gcd_b_tm = mk_numeral candle_adaptive_gcd_b;;

let candle_adaptive_gcd_first_state_tm =
  list_mk_comb
    (`candle_cv_num_gcd_state_chunk`,
     [mk_comb (`Cexp_num`,candle_adaptive_gcd_a_tm);
      mk_comb (`Cexp_num`,candle_adaptive_gcd_b_tm)]);;

let candle_adaptive_gcd_first_state =
  compute candle_adaptive_gcd_compute_eqs
    candle_adaptive_gcd_first_state_tm;;

let candle_adaptive_gcd_first_state_value =
  rand (concl candle_adaptive_gcd_first_state);;

if hyp candle_adaptive_gcd_first_state <> [] ||
   rand candle_adaptive_gcd_first_state_value = `Cexp_num 0` then
  failwith "adaptive gcd did not preserve its unfinished 128-step state";;

let candle_adaptive_gcd_tm =
  list_mk_comb
    (`candle_cv_num_gcd`,
     [mk_comb (`Cexp_num`,candle_adaptive_gcd_a_tm);
      mk_comb (`Cexp_num`,candle_adaptive_gcd_b_tm)]);;

let candle_adaptive_gcd_result =
  compute candle_adaptive_gcd_compute_eqs candle_adaptive_gcd_tm;;

if hyp candle_adaptive_gcd_result <> [] ||
   rand (concl candle_adaptive_gcd_result) <> `Cexp_num 1` then
  failwith "adaptive gcd continuation did not finish the deep coprime case";;

let candle_adaptive_gcd_common =
  compute candle_adaptive_gcd_compute_eqs
    `candle_cv_num_gcd (Cexp_num 84) (Cexp_num 30)`;;

if hyp candle_adaptive_gcd_common <> [] ||
   rand (concl candle_adaptive_gcd_common) <> `Cexp_num 6` then
  failwith "adaptive gcd changed the ordinary completed-chunk result";;

if hyp candle_cv_num_gcd_correct <> [] then
  failwith "adaptive gcd representation theorem has assumptions";;

print_endline "CANDLE_CV_EXACT_RATIONAL_NORMALIZE_OK";;
