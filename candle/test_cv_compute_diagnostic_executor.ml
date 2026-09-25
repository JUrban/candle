(* Focused exact-output test for the untrusted ordinary compute executor. *)

needs "candle/cv_compute_exact_rational_normalize_extended.ml";;
needs "candle/cv_compute_analytic_expr_jet_prove.ml";;
needs "candle/cv_compute_diagnostic_executor.ml";;

open Candle_cv_exact_rational_core;;
open Candle_cv_exact_rational_normalize;;
open Candle_cv_exact_rational_normalize_extended;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_cv_diagnostic_test_q positive negative denominator_predecessor =
  list_mk_comb
    (`Cexp_pair`,
     [list_mk_comb
       (`Cexp_pair`,
        [mk_comb (`Cexp_num`,mk_numeral positive);
         mk_comb (`Cexp_num`,mk_numeral negative)]);
      mk_comb (`Cexp_num`,mk_numeral denominator_predecessor)]);;

let candle_cv_diagnostic_test_left =
  candle_cv_diagnostic_test_q
    (Num.num_of_string "98765432101234567890")
    (Num.num_of_int 0)
    (Num.num_of_string "999999999999");;

let candle_cv_diagnostic_test_right =
  candle_cv_diagnostic_test_q
    (Num.num_of_int 0)
    (Num.num_of_string "12345678900987654321")
    (Num.num_of_string "999999999999");;

let candle_cv_diagnostic_test_equations =
  candle_cv_q_compute_eqs @
  candle_cv_q_normalized_compute_eqs @
  candle_cv_q_extended_normalized_compute_eqs;;

let candle_cv_diagnostic_test_call =
  list_mk_comb
    (`candle_cv_q_add_normalized_extended`,
     [candle_cv_diagnostic_test_left;candle_cv_diagnostic_test_right]);;

let candle_cv_diagnostic_test_program =
  candle_cv_diagnostic_compile candle_cv_diagnostic_test_equations;;

let candle_cv_diagnostic_test_expression =
  candle_cv_diagnostic_compile_term
    candle_cv_diagnostic_test_program candle_cv_diagnostic_test_call;;

let candle_cv_diagnostic_test_value,candle_cv_diagnostic_test_stats =
  candle_cv_diagnostic_execute
    candle_cv_diagnostic_test_program candle_cv_diagnostic_test_expression;;

let candle_cv_diagnostic_test_term =
  candle_cv_diagnostic_value_term candle_cv_diagnostic_test_value;;

let candle_cv_diagnostic_test_kernel =
  candle_q_dim_analytic_jet_compute
    candle_cv_diagnostic_test_equations candle_cv_diagnostic_test_call;;

let _ =
  candle_cv_diagnostic_stats_line
    "exact-rational-add" candle_cv_diagnostic_test_stats;;

if hyp candle_cv_diagnostic_test_kernel <> [] ||
   not
     (aconv candle_cv_diagnostic_test_term
       (rand (concl candle_cv_diagnostic_test_kernel))) then
  failwith "cv diagnostic executor: exact rational result mismatch";;

print_endline
  "CANDLE_CV_DIAGNOSTIC_EXECUTOR_RESULT equations_exact=1 output_exact=1";;
print_endline "CANDLE_CV_DIAGNOSTIC_EXECUTOR_OK DEVELOPMENT_NON_RELEASE";;
