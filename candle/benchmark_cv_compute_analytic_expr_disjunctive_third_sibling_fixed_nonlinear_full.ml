(* Fixed-nonlinear scan of the retained complete third sibling batch.        *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.                            *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_scan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_fixed_nonlinear_full = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Test_cv_compute_analytic_expr_disjunctive_third_sibling_batch_scan;;

let candle_cv_fsn_full_discriminator_jobs_scan_def = define
 `(candle_cv_fsn_full_discriminator_jobs_scan source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_full_discriminator_jobs_scan source_program
      (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_variable_raw_jobs_check source_program
         (Cexp_pair job (Cexp_num 0)))
       (candle_cv_fsn_full_discriminator_jobs_scan source_program jobs))`;;

let candle_cv_fsn_full_discriminator_jobs_scan_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_full_discriminator_jobs_scan source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_variable_raw_jobs_check source_program
           (Cexp_pair (Cexp_fst jobs) (Cexp_num 0)))
         (candle_cv_fsn_full_discriminator_jobs_scan source_program
           (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_full_discriminator_jobs_scan_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fsn_full_discriminator_jobs_scan_compute_eqs =
  union candle_cv_fixed_nonlinear_compute_eqs
    [SPEC_ALL candle_cv_fsn_full_discriminator_jobs_scan_compute];;

let candle_disjunctive_fsn_full_extract context theorem =
  let operator,args = strip_comb (lhand (concl theorem)) in
  if not (aconv operator `candle_cv_fso_variable_jobs_scan`) ||
     length args <> 2 then
    failwith (context ^ ": retained fixed-outer theorem shape");
  hd args,hd (tl args);;

let candle_disjunctive_fsn_full_program0,
    candle_disjunctive_fsn_full_encoded_jobs0 =
  candle_disjunctive_fsn_full_extract "function 0"
    candle_disjunctive_third_batch_function0_theorem;;

let candle_disjunctive_fsn_full_program1,
    candle_disjunctive_fsn_full_encoded_jobs1 =
  candle_disjunctive_fsn_full_extract "function 1"
    candle_disjunctive_third_batch_function1_theorem;;

let candle_disjunctive_fsn_full_call0 =
  list_mk_comb
    (`candle_cv_fsn_full_discriminator_jobs_scan`,
     [candle_disjunctive_fsn_full_program0;
      candle_disjunctive_fsn_full_encoded_jobs0]);;

let candle_disjunctive_fsn_full_call1 =
  list_mk_comb
    (`candle_cv_fsn_full_discriminator_jobs_scan`,
     [candle_disjunctive_fsn_full_program1;
      candle_disjunctive_fsn_full_encoded_jobs1]);;

let candle_disjunctive_fsn_full_axioms_before = axioms ();;

print_endline
  "CANDLE_CV_FSN_FULL_FUNCTION0_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_fsn_full_theorem0 =
  candle_q_dim_analytic_jet_compute
    candle_cv_fsn_full_discriminator_jobs_scan_compute_eqs
    candle_disjunctive_fsn_full_call0;;
print_endline
  "CANDLE_CV_FSN_FULL_FUNCTION0_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_fsn_full_count0,
    candle_disjunctive_fsn_full_failures0 =
  candle_cv_fso_variable_jobs_scan_decode "fixed nonlinear full function 0"
    (rand (concl candle_disjunctive_fsn_full_theorem0));;

print_endline
  "CANDLE_CV_FSN_FULL_FUNCTION1_BEGIN DEVELOPMENT_NON_RELEASE";;
let candle_disjunctive_fsn_full_theorem1 =
  candle_q_dim_analytic_jet_compute
    candle_cv_fsn_full_discriminator_jobs_scan_compute_eqs
    candle_disjunctive_fsn_full_call1;;
print_endline
  "CANDLE_CV_FSN_FULL_FUNCTION1_END DEVELOPMENT_NON_RELEASE";;

let candle_disjunctive_fsn_full_count1,
    candle_disjunctive_fsn_full_failures1 =
  candle_cv_fso_variable_jobs_scan_decode "fixed nonlinear full function 1"
    (rand (concl candle_disjunctive_fsn_full_theorem1));;

let candle_disjunctive_fsn_full_axioms_after = axioms ();;

let candle_disjunctive_fsn_full_differences count outer fixed =
  List.filter
    (fun index -> List.mem index outer <> List.mem index fixed)
    (0--(count - 1));;

let candle_disjunctive_fsn_full_differences0 =
  candle_disjunctive_fsn_full_differences
    candle_disjunctive_fsn_full_count0
    candle_disjunctive_third_batch_function0_failures
    candle_disjunctive_fsn_full_failures0;;

let candle_disjunctive_fsn_full_differences1 =
  candle_disjunctive_fsn_full_differences
    candle_disjunctive_fsn_full_count1
    candle_disjunctive_third_batch_function1_failures
    candle_disjunctive_fsn_full_failures1;;

let candle_disjunctive_fsn_full_prefix count items =
  let rec take remaining = function
    | _ when remaining = 0 -> []
    | [] -> []
    | head::tail -> head::take (remaining - 1) tail in
  take count items;;

if candle_disjunctive_fsn_full_count0 <>
     length candle_disjunctive_third_batch_function0 ||
   candle_disjunctive_fsn_full_count1 <>
     length candle_disjunctive_third_batch_function1 ||
   hyp candle_disjunctive_fsn_full_theorem0 <> [] ||
   hyp candle_disjunctive_fsn_full_theorem1 <> [] ||
   not
     (aconv (lhand (concl candle_disjunctive_fsn_full_theorem0))
       candle_disjunctive_fsn_full_call0) ||
   not
     (aconv (lhand (concl candle_disjunctive_fsn_full_theorem1))
       candle_disjunctive_fsn_full_call1) ||
   length candle_disjunctive_fsn_full_axioms_after <>
     length candle_disjunctive_fsn_full_axioms_before ||
   not
     (List.for_all
       (fun axiom -> List.mem axiom candle_disjunctive_fsn_full_axioms_before)
       candle_disjunctive_fsn_full_axioms_after) then
  failwith "fixed nonlinear full discriminator: validation failed";;

print_endline
  ("CANDLE_CV_FSN_FULL_OK DEVELOPMENT_NON_RELEASE" ^
   " function0_jobs=" ^ string_of_int candle_disjunctive_fsn_full_count0 ^
   " function0_outer_rejected=" ^
   string_of_int
     (length candle_disjunctive_third_batch_function0_failures) ^
   " function0_fixed_rejected=" ^
   string_of_int (length candle_disjunctive_fsn_full_failures0) ^
   " function0_differing=" ^
   string_of_int (length candle_disjunctive_fsn_full_differences0) ^
   " function0_first_differing=" ^
   candle_cv_fso_variable_jobs_scan_indices_string
     (candle_disjunctive_fsn_full_prefix 32
       candle_disjunctive_fsn_full_differences0) ^
   " function1_jobs=" ^ string_of_int candle_disjunctive_fsn_full_count1 ^
   " function1_outer_rejected=" ^
   string_of_int
     (length candle_disjunctive_third_batch_function1_failures) ^
   " function1_fixed_rejected=" ^
   string_of_int (length candle_disjunctive_fsn_full_failures1) ^
   " function1_differing=" ^
   string_of_int (length candle_disjunctive_fsn_full_differences1) ^
   " function1_first_differing=" ^
   candle_cv_fso_variable_jobs_scan_indices_string
     (candle_disjunctive_fsn_full_prefix 32
       candle_disjunctive_fsn_full_differences1) ^
   " assumptions=0 axiom_growth=0");;

end;;
