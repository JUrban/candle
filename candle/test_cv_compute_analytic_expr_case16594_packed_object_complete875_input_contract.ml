(* ========================================================================== *)
(* Complete genuine case-16594 875-cell input contract.                      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Every row comes from the preserved plan       *)
(* capture with SHA-256                                                       *)
(* 236c4ffa1773b92c80584defa24beeddfb20b59811bc287a4f4770da87ac8e80.      *)
(* The HOL kernel proves both source-correspondence directions for every row  *)
(* and the resulting whole-input contract remains parametric in certificate   *)
(* payload bytes.  One scale-2^40 unit of radius slack is part of the exact   *)
(* accepted numerical profile; it covers outward endpoint rounding without   *)
(* changing the authenticated Flyspeck source boxes.                          *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_complete875_input_contract = struct

open Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support;;

let candle_case16594_complete875_radii_batches,
    candle_case16594_complete875_jobs,
    candle_case16594_complete875_job_geometry,
    candle_case16594_complete875_input_contract =
  candle_case16594_prefix_contract_prove_with_radius_padding 1 875;;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_COMPLETE875_INPUT_CONTRACT_OK cells=875 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
