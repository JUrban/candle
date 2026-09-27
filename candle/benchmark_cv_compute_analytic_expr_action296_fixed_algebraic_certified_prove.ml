(* ========================================================================== *)
(* Proof-producing shared-preparation benchmark on eight genuine NL boxes.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  One authenticated source preparation and one  *)
(* point-expression plan are reused by eight distinct exact subboxes.          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_benchmark_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_prove.ml";;

open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_certified_prove;;

let candle_action296_fixed_algebraic_certified_axioms_before = axioms ();;

let candle_action296_fixed_algebraic_certified_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-algebraic-certified" ^
     " scope=boxes-8 phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_action296_fixed_algebraic_certified_marker
    "proof-producing-batch" "begin";;

let candle_action296_fixed_algebraic_certified_theorems_ref :
    thm list option ref = ref None;;
let _ =
  candle_action296_fixed_algebraic_certified_theorems_ref :=
    Some
      (map
        (fun (variant,lower,upper) ->
          candle_q_dim_taylor_model_fixed_algebraic_certified_prove_box_variant_six
            variant candle_action296_instruction_profile_box_prepared
            lower upper)
        candle_action296_instruction_profile_cases);;

let _ =
  candle_action296_fixed_algebraic_certified_marker
    "proof-producing-batch" "end";;

let candle_action296_fixed_algebraic_certified_theorems () =
  match !candle_action296_fixed_algebraic_certified_theorems_ref with
  | Some theorems -> theorems
  | None ->
      failwith "action296 fixed algebraic certified batch: missing theorems";;

let candle_action296_fixed_algebraic_certified_digest =
  Digest.to_hex
    (Digest.string
      (itlist
        (fun theorem tail -> string_of_thm theorem ^ "\n" ^ tail)
        (candle_action296_fixed_algebraic_certified_theorems ()) ""));;

let candle_action296_fixed_algebraic_certified_axioms_after = axioms ();;

if length candle_action296_instruction_profile_cases <> 8 ||
   length (candle_action296_fixed_algebraic_certified_theorems ()) <> 8 ||
   candle_action296_fixed_algebraic_certified_digest <>
     "4debb8d2adc5f5c2504ce2eaf84bf304" ||
   not
     (List.for_all
       (fun theorem -> hyp theorem = [])
       (candle_action296_fixed_algebraic_certified_theorems ())) ||
   length candle_action296_fixed_algebraic_certified_axioms_after <>
     length candle_action296_fixed_algebraic_certified_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_fixed_algebraic_certified_axioms_before)
       candle_action296_fixed_algebraic_certified_axioms_after) then
  failwith
    "action296 fixed algebraic certified batch: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_CERTIFIED_RESULT boxes=8" ^
   " accepted=8 theorems=8 theorem_digest=" ^
   candle_action296_fixed_algebraic_certified_digest);;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_CERTIFIED_OK DEVELOPMENT_NON_RELEASE";;
