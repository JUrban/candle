(* ========================================================================== *)
(* Exact untrusted point-evaluator regression for analytic certificates.      *)
(*                                                                            *)
(* The fast evaluator has no proof authority: reflected certificate checking *)
(* remains the theorem-producing boundary.  This focused test nevertheless   *)
(* compares every supported rational source operation with the prior kernel  *)
(* reduction oracle, guarding the preparation optimization itself.           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;

open Candle_cv_analytic_expr_point_certificate_prepare;;

let candle_q_point_prepare_test_axioms_before = axioms ();;
let candle_q_point_prepare_test_variables = [`x:real`;`y:real`;`z:real`];;
let candle_q_point_prepare_test_values =
  [`&3 / &2:real`;`&5 / &4:real`;`&7 / &3:real`];;
let candle_q_point_prepare_test_expressions =
  [`x:real`;
   `--x:real`;
   `x + y:real`;
   `x - z:real`;
   `x * z:real`;
   `z / y:real`;
   `inv z:real`;
   `(y pow 5):real`;
   `((--x + y) * inv z + (x - y) pow 2):real`];;

let candle_q_point_prepare_test_compare expression =
  let fast =
    candle_q_point_rational_eval
      candle_q_point_prepare_test_variables
      candle_q_point_prepare_test_values expression in
  let compiled =
    candle_q_point_rational_program_value
      (map rat_of_term candle_q_point_prepare_test_values)
      (candle_q_point_rational_compile
        candle_q_point_prepare_test_variables expression) in
  let instantiated =
    subst
      (map2 (fun variable value -> value,variable)
        candle_q_point_prepare_test_variables
        candle_q_point_prepare_test_values)
      expression in
  let oracle =
    rat_of_term (rand (concl (REAL_RAT_REDUCE_CONV instantiated))) in
  if not (Num.eq_num fast oracle) || not (Num.eq_num compiled oracle) then
    failwith
      ("analytic point certificate evaluator mismatch: " ^
       string_of_term expression);;

let _ =
  do_list candle_q_point_prepare_test_compare
    candle_q_point_prepare_test_expressions;;

let candle_q_point_prepare_test_axioms_after = axioms ();;

if length candle_q_point_prepare_test_axioms_after <>
     length candle_q_point_prepare_test_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_q_point_prepare_test_axioms_before)
       candle_q_point_prepare_test_axioms_after) then
  failwith "analytic point certificate evaluator changed the axiom set";;

print_endline
  "CANDLE_CV_ANALYTIC_POINT_CERTIFICATE_PREPARE_OK cases=9 compiled=9";;
