(* Untrusted bounded diagnostic for the genuine matan target's escape branch. *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_prepare.ml";;

open Candle_cv_analytic_expr_matan_domain_probe;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;

module Probe_cv_compute_analytic_expr_matan_genuine_escape_range = struct

let escape_source =
  let operator,arguments = strip_comb escape_relation in
  if not (aconv operator `(<):real->real->bool`) then
    failwith "genuine matan escape range: relation shape";
  match arguments with
  | [source;zero] when aconv zero `&0:real` -> source
  | _ -> failwith "genuine matan escape range: bound shape";;

let escape_environment =
  zip ordered_variables (zip lower_num upper_num);;

let escape_lower,escape_upper =
  candle_nl_matan_interval_eval escape_environment escape_source;;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ESCAPE_RANGE_RESULT" ^
   " DEVELOPMENT_NON_RELEASE_UNTRUSTED" ^
   " source_id=" ^ source_id ^
   " lower=" ^ Num.string_of_num escape_lower ^
   " upper=" ^ Num.string_of_num escape_upper ^
   " upper_negative=" ^
     (if Num.lt_num escape_upper (Num.num_of_int 0) then "true"
      else "false"));;
print_endline "CANDLE_CV_MATAN_GENUINE_ESCAPE_RANGE_OK";;

end;;
