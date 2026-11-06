(* ========================================================================== *)
(* Genuine case-16594 four-cell input contract with one fixed-word radius    *)
(* padding unit.  This is the bounded preflight for the complete 875-cell    *)
(* accepted numerical profile.                                               *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix4_radius_pad1_input_contract = struct

open Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support;;

let candle_case16594_prefix4_radius_pad1_radii_batches,
    candle_case16594_prefix4_radius_pad1_jobs,
    candle_case16594_prefix4_radius_pad1_job_geometry,
    candle_case16594_prefix4_radius_pad1_input_contract =
  candle_case16594_prefix_contract_prove_with_radius_padding 1 4;;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_PREFIX4_RADIUS_PAD1_INPUT_CONTRACT_OK cells=4 radius_padding_units=1 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
