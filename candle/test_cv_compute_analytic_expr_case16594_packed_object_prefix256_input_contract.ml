(* ========================================================================== *)
(* Genuine case-16594 256-cell input contract from the sealed plan capture.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the final bounded scale probe before  *)
(* attempting the complete 875-row contract.                                  *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix256_input_contract = struct

open Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support;;

let candle_case16594_prefix256_radii_batches,
    candle_case16594_prefix256_jobs,
    candle_case16594_prefix256_job_geometry,
    candle_case16594_prefix256_input_contract =
  candle_case16594_prefix_contract_prove 256;;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_PREFIX256_INPUT_CONTRACT_OK cells=256 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
