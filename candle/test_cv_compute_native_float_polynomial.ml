needs "candle/compute.ml";;
needs "candle/cv_compute_native_float_polynomial.ml";;

open Candle_cv_native_float_core;;
open Candle_cv_native_float_polynomial;;

let candle_nf_poly_test_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 ([]:num list))))))`;;
let candle_nf_poly_test_fuel_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_poly_test_fuel));;

(* Six first-derivative products and the 21 lower-triangular second-derivative
   products of a dimension-six Taylor bound. Triple factors exercise the
   coarser second-order batch rather than only a binary arithmetic primitive. *)
let candle_nf_poly_test_terms =
 `[[2;101]; [3;103]; [5;107]; [7;109]; [11;113]; [13;127];
   [2;2;131]; [3;2;137]; [3;3;139]; [5;2;149]; [5;3;151];
   [5;5;157]; [7;2;163]; [7;3;167]; [7;5;173]; [7;7;179];
   [11;2;181]; [11;3;191]; [11;5;193]; [11;7;197]; [11;11;199];
   [13;2;211]; [13;3;223]; [13;5;227]; [13;7;229]; [13;11;233];
   [13;13;239]]`;;

let candle_nf_poly_test_terms_rep =
  REWRITE_CONV[candle_nf_num_lists_def; candle_nf_num_list_def]
    (mk_comb (`candle_nf_num_lists`,candle_nf_poly_test_terms));;

let candle_nf_poly_test_compute =
  compute candle_cv_nf_polynomial_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_polynomial_round_hi`,
       [`Cexp_num 200`; `Cexp_num 10000`;
        rand (concl candle_nf_poly_test_fuel_rep); `Cexp_num 17`;
        rand (concl candle_nf_poly_test_terms_rep)]));;

if hyp candle_nf_poly_test_compute <> [] then
  failwith "native-float polynomial computation has assumptions";;

let candle_nf_poly_test_correct =
  SPECL
    [candle_nf_poly_test_fuel; `200`; `10000`; `17`;
     candle_nf_poly_test_terms]
    candle_cv_nf_polynomial_round_hi_correct;;

if hyp candle_nf_poly_test_correct <> [] ||
   hyp candle_nf_polynomial_round_hi_sound <> [] then
  failwith "native-float polynomial theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_POLYNOMIAL_OK";;
