needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_mul.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_mul;;

let candle_nf_mul_test_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 ([]:num list))))`;;
let candle_nf_mul_test_fuel_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_mul_test_fuel));;

let candle_nf_mul_test_x = `(1234567,8)` and
    candle_nf_mul_test_y = `(7654321,9)`;;

let candle_nf_mul_test_lo =
  compute candle_cv_nf_mul_round_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_mul_round_lo`,
       [`Cexp_num 100`; `Cexp_num 10000`;
        rand (concl candle_nf_mul_test_fuel_rep);
        `Cexp_pair (Cexp_num 1234567) (Cexp_num 8)`;
        `Cexp_pair (Cexp_num 7654321) (Cexp_num 9)`]));;

let candle_nf_mul_test_hi =
  compute candle_cv_nf_mul_round_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_mul_round_hi`,
       [`Cexp_num 100`; `Cexp_num 10000`;
        rand (concl candle_nf_mul_test_fuel_rep);
        `Cexp_pair (Cexp_num 1234567) (Cexp_num 8)`;
        `Cexp_pair (Cexp_num 7654321) (Cexp_num 9)`]));;

if hyp candle_nf_mul_test_lo <> [] || hyp candle_nf_mul_test_hi <> [] then
  failwith "native-float multiply/round computation has assumptions";;

let candle_nf_mul_test_lo_correct =
  SPECL
    [candle_nf_mul_test_fuel; `100`; `10000`;
     candle_nf_mul_test_x; candle_nf_mul_test_y]
    candle_cv_nf_mul_round_lo_correct and
    candle_nf_mul_test_hi_correct =
      SPECL
        [candle_nf_mul_test_fuel; `100`; `10000`;
         candle_nf_mul_test_x; candle_nf_mul_test_y]
        candle_cv_nf_mul_round_hi_correct;;

if hyp candle_nf_mul_test_lo_correct <> [] ||
   hyp candle_nf_mul_test_hi_correct <> [] ||
   hyp candle_nf_mul_round_lo_sound <> [] ||
   hyp candle_nf_mul_round_hi_sound <> [] ||
   hyp candle_nf_mul_pair_value <> [] then
  failwith "native-float multiply/round theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_MUL_OK";;
