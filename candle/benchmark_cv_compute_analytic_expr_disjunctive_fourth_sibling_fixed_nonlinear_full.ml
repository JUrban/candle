(* Fixed-nonlinear scan of the complete fourth sibling batch.               *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.                            *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_nonlinear.ml";;
needs "candle/test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_fourth_sibling_fixed_nonlinear_full = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_nonlinear;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_scan;;
open Test_cv_compute_analytic_expr_disjunctive_fourth_sibling_batch_scan;;

let candle_cv_fsn_fourth_discriminator_jobs_scan_def = define
 `(candle_cv_fsn_fourth_discriminator_jobs_scan source_program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_fsn_fourth_discriminator_jobs_scan source_program
      (Cexp_pair job jobs) =
     Cexp_pair
       (candle_cv_fsn_variable_raw_jobs_check source_program
         (Cexp_pair job (Cexp_num 0)))
       (candle_cv_fsn_fourth_discriminator_jobs_scan source_program jobs))`;;

let candle_cv_fsn_fourth_discriminator_jobs_scan_compute = prove
 (`!source_program jobs.
     candle_cv_fsn_fourth_discriminator_jobs_scan source_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (candle_cv_fsn_variable_raw_jobs_check source_program
           (Cexp_pair (Cexp_fst jobs) (Cexp_num 0)))
         (candle_cv_fsn_fourth_discriminator_jobs_scan source_program
           (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC
    [candle_cv_fsn_fourth_discriminator_jobs_scan_def;
     cexp_ispair_def;cexp_if_def;cexp_fst_def;cexp_snd_def]);;

let candle_cv_fsn_fourth_discriminator_jobs_scan_compute_eqs =
  union candle_cv_fixed_nonlinear_compute_eqs
    [SPEC_ALL candle_cv_fsn_fourth_discriminator_jobs_scan_compute];;

let candle_disjunctive_fsn_fourth_extract context theorem =
  let operator,args = strip_comb (lhand (concl theorem)) in
  if not (aconv operator `candle_cv_fso_variable_jobs_scan`) ||
     length args <> 2 then
    failwith (context ^ ": retained fixed-outer theorem shape");
  hd args,hd (tl args);;

let candle_disjunctive_fsn_fourth_differences count outer fixed =
  List.filter
    (fun index -> List.mem index outer <> List.mem index fixed)
    (0--(count - 1));;

let candle_disjunctive_fsn_fourth_prefix count items =
  let rec take remaining = function
    | _ when remaining = 0 -> []
    | [] -> []
    | head::tail -> head::take (remaining - 1) tail in
  take count items;;

(* Keep the large computed theorems and verdict terms local.  This avoids   *)
(* serializing them into the transcript after the useful result marker.     *)
let _ =
  let program0,encoded_jobs0 =
    candle_disjunctive_fsn_fourth_extract "function 0"
      candle_disjunctive_fourth_batch_function0_theorem
  and program1,encoded_jobs1 =
    candle_disjunctive_fsn_fourth_extract "function 1"
      candle_disjunctive_fourth_batch_function1_theorem in
  let call0 =
    list_mk_comb
      (`candle_cv_fsn_fourth_discriminator_jobs_scan`,
       [program0;encoded_jobs0])
  and call1 =
    list_mk_comb
      (`candle_cv_fsn_fourth_discriminator_jobs_scan`,
       [program1;encoded_jobs1]) in
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_FSN_FOURTH_FUNCTION0_BEGIN DEVELOPMENT_NON_RELEASE";
  let theorem0 =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsn_fourth_discriminator_jobs_scan_compute_eqs call0 in
  print_endline
    "CANDLE_CV_FSN_FOURTH_FUNCTION0_END DEVELOPMENT_NON_RELEASE";
  let count0,failures0 =
    candle_cv_fso_variable_jobs_scan_decode "fixed nonlinear fourth function 0"
      (rand (concl theorem0)) in
  print_endline
    "CANDLE_CV_FSN_FOURTH_FUNCTION1_BEGIN DEVELOPMENT_NON_RELEASE";
  let theorem1 =
    candle_q_dim_analytic_jet_compute
      candle_cv_fsn_fourth_discriminator_jobs_scan_compute_eqs call1 in
  print_endline
    "CANDLE_CV_FSN_FOURTH_FUNCTION1_END DEVELOPMENT_NON_RELEASE";
  let count1,failures1 =
    candle_cv_fso_variable_jobs_scan_decode "fixed nonlinear fourth function 1"
      (rand (concl theorem1)) in
  let differences0 =
    candle_disjunctive_fsn_fourth_differences count0
      candle_disjunctive_fourth_batch_function0_failures failures0
  and differences1 =
    candle_disjunctive_fsn_fourth_differences count1
      candle_disjunctive_fourth_batch_function1_failures failures1 in
  let axioms_after = axioms () in
  if count0 <> length candle_disjunctive_fourth_batch_function0 ||
     count1 <> length candle_disjunctive_fourth_batch_function1 ||
     hyp theorem0 <> [] || hyp theorem1 <> [] ||
     not (aconv (lhand (concl theorem0)) call0) ||
     not (aconv (lhand (concl theorem1)) call1) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before) axioms_after) then
    failwith "fixed nonlinear fourth discriminator: validation failed";
  print_endline
    ("CANDLE_CV_FSN_FOURTH_OK DEVELOPMENT_NON_RELEASE" ^
     " function0_jobs=" ^ string_of_int count0 ^
     " function0_outer_rejected=" ^
     string_of_int
       (length candle_disjunctive_fourth_batch_function0_failures) ^
     " function0_fixed_rejected=" ^ string_of_int (length failures0) ^
     " function0_differing=" ^ string_of_int (length differences0) ^
     " function0_first_differing=" ^
     candle_cv_fso_variable_jobs_scan_indices_string
       (candle_disjunctive_fsn_fourth_prefix 32 differences0) ^
     " function1_jobs=" ^ string_of_int count1 ^
     " function1_outer_rejected=" ^
     string_of_int
       (length candle_disjunctive_fourth_batch_function1_failures) ^
     " function1_fixed_rejected=" ^ string_of_int (length failures1) ^
     " function1_differing=" ^ string_of_int (length differences1) ^
     " function1_first_differing=" ^
     candle_cv_fso_variable_jobs_scan_indices_string
       (candle_disjunctive_fsn_fourth_prefix 32 differences1) ^
     " assumptions=0 axiom_growth=0");;

end;;
