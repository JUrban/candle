(* ========================================================================== *)
(* Proof-producing fixed-nonlinear check of one genuine action-296 box.      *)
(* DEVELOPMENT / NON-RELEASE.                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_benchmark_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear_certified_prove.ml";;

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear_certified_prove;;

let candle_action296_fixed_nonlinear_first_axioms_before = axioms ();;
let candle_action296_fixed_nonlinear_first_started = Unix.gettimeofday ();;

let candle_action296_fixed_nonlinear_first_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-nonlinear-certified" ^
     " scope=box-1 phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=action296-fixed-nonlinear-certified" ^
         " phase=" ^ event));;

let candle_action296_fixed_nonlinear_first_variant,
    candle_action296_fixed_nonlinear_first_lower,
    candle_action296_fixed_nonlinear_first_upper =
  hd candle_action296_instruction_profile_cases;;

let _ =
  candle_action296_fixed_nonlinear_first_marker
    "proof-producing-first" "begin";;

let candle_action296_fixed_nonlinear_first_theorem =
  candle_q_dim_taylor_model_fixed_nonlinear_certified_prove_box_variant_six
    candle_action296_fixed_nonlinear_first_variant
    candle_action296_instruction_profile_box_prepared
    candle_action296_fixed_nonlinear_first_lower
    candle_action296_fixed_nonlinear_first_upper;;

let _ =
  candle_action296_fixed_nonlinear_first_marker
    "proof-producing-first" "end";;

let candle_action296_fixed_nonlinear_first_digest =
  Digest.to_hex
    (Digest.string
      (string_of_thm candle_action296_fixed_nonlinear_first_theorem));;

let candle_action296_fixed_nonlinear_first_axioms_after = axioms ();;

if length candle_action296_instruction_profile_cases <> 8 ||
   hyp candle_action296_fixed_nonlinear_first_theorem <> [] ||
   length candle_action296_fixed_nonlinear_first_axioms_after <>
     length candle_action296_fixed_nonlinear_first_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_nonlinear_first_axioms_before)
       candle_action296_fixed_nonlinear_first_axioms_after) then
  failwith
    "action296 fixed nonlinear certified first box: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_NONLINEAR_CERTIFIED_FIRST_RESULT" ^
   " boxes=1 accepted=1 theorems=1 theorem_md5=" ^
   candle_action296_fixed_nonlinear_first_digest ^
   " total_seconds=" ^
   string_of_float
     (Unix.gettimeofday () -. candle_action296_fixed_nonlinear_first_started));;
print_endline
  "CANDLE_CV_ACTION296_FIXED_NONLINEAR_CERTIFIED_FIRST_OK DEVELOPMENT_NON_RELEASE";;
