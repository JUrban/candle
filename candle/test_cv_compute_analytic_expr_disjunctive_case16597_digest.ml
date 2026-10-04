(* Pin the exact theorem identity after the expensive reflected computation. *)

needs "candle/test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16597_digest = struct

open Test_cv_compute_analytic_expr_disjunctive_case16597_shared_complete;;

let candle_disjunctive_case16597_expected_digest =
  "d5430891981683e6fc87e08eb2b2643e";;

if candle_disjunctive_case16597_digest <>
     candle_disjunctive_case16597_expected_digest then
  failwith "case16597 digest: exact theorem identity drift";;

print_endline
  ("CANDLE_CV_CASE16597_DIGEST_OK DEVELOPMENT_NON_RELEASE" ^
   " theorem_digest=" ^ candle_disjunctive_case16597_digest);;

end;;
