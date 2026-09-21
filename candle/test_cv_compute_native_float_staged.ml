needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_staged.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_staged;;

let candle_nf_staged_test_round_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0
    (CONS 0 (CONS 0 ([]:num list))))))))`;;
let candle_nf_staged_test_power_fuel =
  `CONS 0 ([]:num list)`;;

let candle_nf_staged_test_round_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_staged_test_round_fuel));;
let candle_nf_staged_test_power_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_staged_test_power_fuel));;

let candle_nf_staged_test_x = `(12345,5)` and
    candle_nf_staged_test_y = `(6789,4)`;;

let candle_nf_staged_test_add =
  compute candle_cv_nf_staged_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_add_round_hi`,
       [`Cexp_num 10`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_test_round_rep);
        rand (concl candle_nf_staged_test_power_rep);
        `Cexp_pair (Cexp_num 12345) (Cexp_num 5)`;
        `Cexp_pair (Cexp_num 6789) (Cexp_num 4)`]));;

let candle_nf_staged_test_mul =
  compute candle_cv_nf_staged_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_scaled_mul_round_hi`,
       [`Cexp_num 10`; `Cexp_num 5`; `Cexp_num 1000`;
        rand (concl candle_nf_staged_test_round_rep);
        `Cexp_pair (Cexp_num 12345) (Cexp_num 5)`;
        `Cexp_pair (Cexp_num 6789) (Cexp_num 4)`]));;

let candle_nf_staged_test_add_correct =
  SPECL
    [`10`; `1000`; candle_nf_staged_test_round_fuel;
     candle_nf_staged_test_power_fuel;
     candle_nf_staged_test_x; candle_nf_staged_test_y]
    candle_cv_nf_add_round_hi_correct;;

let candle_nf_staged_test_mul_correct =
  SPECL
    [`10`; `5`; `1000`; candle_nf_staged_test_round_fuel;
     candle_nf_staged_test_x; candle_nf_staged_test_y]
    candle_cv_nf_scaled_mul_round_hi_correct;;

let candle_nf_staged_test_add_power_complete =
  prove
   (`candle_nf_add_power_complete [0] (12345,5) (6789,4)`,
    REWRITE_TAC[candle_nf_add_power_complete_def; LENGTH; SND] THEN
    NUM_REDUCE_TAC);;

let candle_nf_staged_test_add_sound =
  MP
    (SPECL
      [`10`; `1000`; candle_nf_staged_test_round_fuel;
       candle_nf_staged_test_power_fuel;
       candle_nf_staged_test_x; candle_nf_staged_test_y]
      candle_nf_add_round_hi_sound)
    (CONJ (EQT_ELIM (NUM_REDUCE_CONV `~(10 = 0)`))
      candle_nf_staged_test_add_power_complete);;

let candle_nf_staged_test_mul_sound =
  MP
    (SPECL
      [`10`; `5`; `1000`; candle_nf_staged_test_round_fuel;
       candle_nf_staged_test_x; candle_nf_staged_test_y]
      candle_nf_scaled_mul_round_hi_sound)
    (EQT_ELIM (NUM_REDUCE_CONV
      `~(10 = 0) /\ 5 <= SND (12345,5) + SND (6789,4)`));;

if hyp candle_nf_staged_test_add <> [] ||
   hyp candle_nf_staged_test_mul <> [] ||
   hyp candle_nf_staged_test_add_correct <> [] ||
   hyp candle_nf_staged_test_mul_correct <> [] ||
   hyp candle_nf_staged_test_add_sound <> [] ||
   hyp candle_nf_staged_test_mul_sound <> []
then failwith "staged native-float theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_STAGED_OK";;
