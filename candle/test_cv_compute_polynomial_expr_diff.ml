needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_diff.ml";;

open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_dim_derivatives;;
open Candle_cv_polynomial_expr_dim_calculus;;
open Candle_cv_polynomial_expr_diff;;

let candle_poly_diff_fixture =
 `Candle_poly_add
    (Candle_poly_mul (Candle_poly_var 0) (Candle_poly_var 5))
    (Candle_poly_square (Candle_poly_var 2))`;;

let rec candle_repeat_conv n conv =
  if n = 0 then ALL_CONV
  else conv THENC candle_repeat_conv (n - 1) conv;;

let candle_poly_diff_fixture_conv =
  candle_repeat_conv 12
   (SIMP_CONV[candle_poly_diff2_def; candle_poly_diff_def; ARITH]);;

let candle_poly_compile_fixture_conv =
  candle_repeat_conv 12
   (SIMP_CONV[candle_poly_compile_def; APPEND]);;

let candle_poly_diff_fixture_first =
  rand
   (concl
     (candle_poly_diff_fixture_conv
       (list_mk_comb
         (`candle_poly_diff`,[`0`;candle_poly_diff_fixture]))));;

let candle_poly_diff_fixture_second =
  rand
   (concl
     (candle_poly_diff_fixture_conv
       (list_mk_comb
         (`candle_poly_diff2`,
          [`5`;`0`;candle_poly_diff_fixture]))));;

let candle_poly_diff_fixture_first_program =
  rand
   (concl
     (candle_poly_compile_fixture_conv
       (mk_comb (`candle_poly_compile`,candle_poly_diff_fixture_first))));;

let candle_poly_diff_fixture_second_program =
  rand
   (concl
     (candle_poly_compile_fixture_conv
       (mk_comb (`candle_poly_compile`,candle_poly_diff_fixture_second))));;

if length (dest_list candle_poly_diff_fixture_first_program) = 0 ||
   length (dest_list candle_poly_diff_fixture_second_program) = 0
then failwith "symbolic derivative compiler produced an empty program";;

let candle_poly_diff_fixture_first_correct =
  SPECL
   [candle_poly_diff_fixture;
    `[x1:real;x2;x3;x4;x5;x6]`; `0`]
   candle_poly_diff_compile_real_program;;

let candle_poly_diff_fixture_second_correct =
  SPECL
   [candle_poly_diff_fixture;
    `[x1:real;x2;x3;x4;x5;x6]`; `0`; `5`]
   candle_poly_diff2_compile_real_program;;

if hyp candle_poly_diff_valid <> [] ||
   hyp candle_poly_diff2_valid <> [] ||
   hyp candle_poly_diff_value_fun <> [] ||
   hyp candle_poly_diff_d_fun <> [] ||
   hyp candle_poly_diff2_value_fun <> [] ||
   hyp candle_poly_diff_value_list <> [] ||
   hyp candle_poly_diff_d_list <> [] ||
   hyp candle_poly_diff2_value_list <> [] ||
   hyp candle_poly_diff_compile_real_program <> [] ||
   hyp candle_poly_diff2_compile_real_program <> [] ||
   hyp candle_poly_diff_interval_sound <> [] ||
   hyp candle_poly_diff2_interval_sound <> [] ||
   hyp candle_poly_diff_fixture_first_correct <> [] ||
   hyp candle_poly_diff_fixture_second_correct <> []
then failwith "symbolic polynomial derivative theorem assumptions mismatch";;

print_endline
 ("CANDLE_CV_POLYNOMIAL_EXPR_DIFF first_program=" ^
  string_of_int (length (dest_list candle_poly_diff_fixture_first_program)) ^
  " second_program=" ^
  string_of_int (length (dest_list candle_poly_diff_fixture_second_program)));;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIFF_OK";;
