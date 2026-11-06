(* ========================================================================== *)
(* Genuine case-16594 sixty-four-cell input contract from the sealed capture. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This measures the next bounded scale-up of    *)
(* the generic whole-input contract.                                          *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support.ml";;

module Test_cv_compute_analytic_expr_case16594_packed_object_prefix64_input_contract = struct

open Test_cv_compute_analytic_expr_case16594_packed_object_prefix_contract_support;;

let candle_case16594_prefix64_radii_batches,
    candle_case16594_prefix64_jobs,
    candle_case16594_prefix64_job_geometry,
    candle_case16594_prefix64_input_contract =
  candle_case16594_prefix_contract_prove 64;;

print_endline
  "CANDLE_CV_CASE16594_PACKED_OBJECT_PREFIX64_INPUT_CONTRACT_OK cells=64 certificate_payload=parametric assumptions=0 DEVELOPMENT_NON_RELEASE";;

end;;
