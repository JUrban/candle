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

(* Exercise authenticated exponent alignment on the same Taylor shape.  The
   target is 17 and the per-monomial exponent differences range from 1 to 4;
   unary fuel makes those differences explicit while keeping power/product/sum
   evaluation inside Kernel.compute. *)
let candle_nf_fueled_test_fuel =
  `CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0 (CONS 0
    (CONS 0 (CONS 0 (CONS 0 (CONS 0 ([]:num list))))))))))`;;

let candle_nf_fueled_test_terms =
 `[[2,8;101,10]; [3,8;103,11]; [5,9;107,11];
   [7,9;109,12]; [11,7;113,11]; [13,10;127,10];
   [2,5;2,6;131,7]; [3,5;2,6;137,8]; [3,5;3,7;139,8];
   [5,6;2,7;149,8]; [5,5;3,6;151,7]; [5,5;5,6;157,8];
   [7,5;2,7;163,8]; [7,6;3,7;167,8]; [7,5;5,6;173,7];
   [7,5;7,6;179,8]; [11,5;2,7;181,8]; [11,6;3,7;191,8];
   [11,5;5,6;193,7]; [11,5;7,6;197,8]; [11,5;11,7;199,8];
   [13,6;2,7;211,8]; [13,5;3,6;223,7]; [13,5;5,6;227,8];
   [13,5;7,7;229,8]; [13,6;11,7;233,8];
   [13,5;13,6;239,7]]:((num#num)list)list`;;

let candle_nf_fueled_test_items =
 `[([2;101],[0]); ([3;103],[0;0]); ([5;107],[0;0;0]);
   ([7;109],[0;0;0;0]); ([11;113],[0]); ([13;127],[0;0;0]);
   ([2;2;131],[0]); ([3;2;137],[0;0]); ([3;3;139],[0;0;0]);
   ([5;2;149],[0;0;0;0]); ([5;3;151],[0]);
   ([5;5;157],[0;0]); ([7;2;163],[0;0;0]);
   ([7;3;167],[0;0;0;0]); ([7;5;173],[0]);
   ([7;7;179],[0;0]); ([11;2;181],[0;0;0]);
   ([11;3;191],[0;0;0;0]); ([11;5;193],[0]);
   ([11;7;197],[0;0]); ([11;11;199],[0;0;0]);
   ([13;2;211],[0;0;0;0]); ([13;3;223],[0]);
   ([13;5;227],[0;0]); ([13;7;229],[0;0;0]);
   ([13;11;233],[0;0;0;0]); ([13;13;239],[0])]
   :(num list#num list)list`;;

let candle_nf_fueled_test_alignment_tm =
  list_mk_comb
    (`candle_nf_fueled_alignment`,
     [`17`; candle_nf_fueled_test_terms; candle_nf_fueled_test_items]);;

let candle_nf_fueled_test_alignment_rewrite =
  REWRITE_CONV
    [candle_nf_fueled_alignment_def; candle_nf_product_def;
     candle_nf_monomial_mantissa_def; candle_nf_monomial_exponent_def;
     FST; SND; LENGTH]
    candle_nf_fueled_test_alignment_tm;;

let candle_nf_fueled_test_alignment =
  EQT_ELIM
    (TRANS candle_nf_fueled_test_alignment_rewrite
      (NUM_REDUCE_CONV
        (rand (concl candle_nf_fueled_test_alignment_rewrite))));;

let candle_nf_fueled_test_fuel_rep =
  REWRITE_CONV[candle_nf_fuel_def]
    (mk_comb (`candle_nf_fuel`,candle_nf_fueled_test_fuel));;

let candle_nf_fueled_test_items_rep =
  REWRITE_CONV
    [candle_nf_fueled_items_def; candle_nf_fueled_item_def;
     candle_nf_num_list_def; candle_nf_fuel_def; FST; SND]
    (mk_comb (`candle_nf_fueled_items`,candle_nf_fueled_test_items));;

let candle_nf_fueled_test_compute =
  compute candle_cv_nf_fueled_polynomial_compute_eqs
    (list_mk_comb
      (`candle_cv_nf_fueled_polynomial_round_hi`,
       [`Cexp_num 16`; `Cexp_num 65536`;
        rand (concl candle_nf_fueled_test_fuel_rep); `Cexp_num 17`;
        rand (concl candle_nf_fueled_test_items_rep)]));;

let candle_nf_fueled_test_correct =
  SPECL
    [candle_nf_fueled_test_fuel; `16`; `65536`; `17`;
     candle_nf_fueled_test_items]
    candle_cv_nf_fueled_polynomial_round_hi_correct;;

let candle_nf_fueled_test_correct =
  PURE_REWRITE_RULE
    [candle_nf_fueled_test_fuel_rep; candle_nf_fueled_test_items_rep]
    candle_nf_fueled_test_correct;;

let candle_nf_fueled_test_result =
  TRANS (SYM candle_nf_fueled_test_correct)
    candle_nf_fueled_test_compute;;

let candle_nf_fueled_test_round =
  REWRITE_RULE
    [candle_nf_pair_roundtrip; candle_nf_decode_pair_def;
     candle_nf_decode_num_def]
    (AP_TERM `candle_nf_decode_pair` candle_nf_fueled_test_result);;

let candle_nf_fueled_test_sound =
  SPECL
    [candle_nf_fueled_test_fuel; `16`; `65536`; `17`;
     candle_nf_fueled_test_terms; candle_nf_fueled_test_items]
    candle_nf_fueled_polynomial_round_hi_sound;;

let candle_nf_fueled_test_sound =
  MP candle_nf_fueled_test_sound
    (CONJ
      (EQT_ELIM (NUM_REDUCE_CONV `~(16 = 0)`))
      candle_nf_fueled_test_alignment);;

let candle_nf_fueled_test_sound =
  REWRITE_RULE[candle_nf_fueled_test_round; FST; SND]
    candle_nf_fueled_test_sound;;

if hyp candle_nf_fueled_test_compute <> [] ||
   hyp candle_nf_fueled_test_sound <> [] then
  failwith "fueled native-float polynomial theorem has assumptions";;

print_endline "CANDLE_CV_NATIVE_FLOAT_POLYNOMIAL_OK";;
