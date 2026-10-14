(* Exact root-domain identity regression for genuine case-10173. *)

needs "candle/cv_compute_analytic_expr_case10173_historical_registered_domain_prove.ml";;
needs "candle/cv_compute_analytic_expr_case10173_leaf_grouping_fixture.ml";;

module Test_cv_compute_analytic_expr_case10173_historical_registered_domain_prove = struct

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_case10173_historical_registered_domain_prove;;

let _ =
  let axioms_before = axioms () in
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds
      candle_case10173_leaf_grouping_root_domain in
  let root_boxes = candle_poly_fixture_q_boxes lower upper in
  let identity =
    candle_case10173_historical_registered_domain_prove root_boxes in
  let axioms_after = axioms () in
  if hyp identity <> [] ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 registered domain prove test: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_DOMAIN_PROVE_TEST_OK DEVELOPMENT_NON_RELEASE dimensions=6 assumptions=0 axiom_growth=0";;

end;;
