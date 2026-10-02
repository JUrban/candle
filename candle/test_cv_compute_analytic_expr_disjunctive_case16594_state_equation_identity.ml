(* Fingerprint the exact theorem lists supplied to Kernel.compute in the
   matched checker-state discriminator.  DEVELOPMENT / NON-RELEASE only. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute.ml";;

module Test_cv_compute_analytic_expr_disjunctive_case16594_state_equation_identity = struct

open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;

let candle_case16594_state_equation_identity_digest theorems =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map (fun theorem -> string_of_term (concl theorem)) theorems)));;

let _ =
  print_endline
    ("CANDLE_CV_CASE16594_STATE_EQUATION_IDENTITY" ^
     " compute_init_count=" ^ string_of_int (length COMPUTE_INIT_THMS) ^
     " compute_init_md5=" ^
       candle_case16594_state_equation_identity_digest COMPUTE_INIT_THMS ^
     " raw_count=" ^
       string_of_int (length candle_cv_fso_variable_raw_compute_eqs) ^
     " raw_md5=" ^
       candle_case16594_state_equation_identity_digest
         candle_cv_fso_variable_raw_compute_eqs);
  print_endline
    "CANDLE_CV_CASE16594_STATE_EQUATION_IDENTITY_OK DEVELOPMENT_NON_RELEASE";;

end;;
