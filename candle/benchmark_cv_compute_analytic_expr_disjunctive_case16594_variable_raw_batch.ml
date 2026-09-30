(* Real case-16594 discriminator for the canonical raw-certificate boundary. *)

needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_case16594_variable_raw_batch = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Candle_cv_analytic_expr_disjunctive_case16594_family_prove;;
open Candle_cv_analytic_expr_disjunctive_family_engine;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;

let candle_disjunctive_case16594_variable_raw_axioms_before = axioms ();;

Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
  (fun event ->
    print_endline
      ("CANDLE_CERT_PROFILE lane=disjunctive-case16594-variable-raw" ^
       " phase=" ^ event));;

let rec candle_disjunctive_case16594_variable_raw_take count items =
  if count = 0 then []
  else
    match items with
    | [] -> failwith "case16594 variable raw batch: short leaf list"
    | head :: tail ->
        head ::
        candle_disjunctive_case16594_variable_raw_take (count - 1) tail;;

let candle_disjunctive_case16594_variable_raw_make_cell (_,domain) =
  let lower,upper =
    candle_disjunctive_fixed_outer_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      candle_disjunctive_case16594_engine_state.family_engine_point_plan
      lower upper in
  let box_intervals =
    map (candle_disjunctive_fixed_outer_widen 5 4) center_intervals in
  {variable_batch_box_intervals = box_intervals;
   variable_batch_stable_cell =
     {stable_batch_center_intervals = center_intervals;
      stable_batch_lower = lower;
      stable_batch_upper = upper}};;

let candle_disjunctive_case16594_variable_raw_cells_32 =
  map candle_disjunctive_case16594_variable_raw_make_cell
    (candle_disjunctive_case16594_variable_raw_take 32
      candle_disjunctive_case16594_engine_state.family_engine_leaves);;

let candle_disjunctive_case16594_variable_raw_run count =
  candle_q_dim_taylor_model_fixed_outer_variable_raw_prove_six
    candle_disjunctive_case16594_engine_state.family_engine_prepared
    (candle_disjunctive_case16594_variable_raw_take count
      candle_disjunctive_case16594_variable_raw_cells_32);;

let candle_disjunctive_case16594_variable_raw_result_1 =
  candle_disjunctive_case16594_variable_raw_run 1;;
let candle_disjunctive_case16594_variable_raw_result_8 =
  candle_disjunctive_case16594_variable_raw_run 8;;
let candle_disjunctive_case16594_variable_raw_result_32 =
  candle_disjunctive_case16594_variable_raw_run 32;;

let candle_disjunctive_case16594_variable_raw_compute encoded =
  let prepared =
    candle_disjunctive_case16594_engine_state.family_engine_prepared in
  candle_q_dim_analytic_jet_compute
    candle_cv_fso_variable_raw_compute_eqs
    (list_mk_comb
      (`candle_cv_fso_variable_raw_jobs_check`,
       [prepared.program_representation_term;encoded]));;

let rec candle_disjunctive_case16594_variable_raw_bad_terminator encoded =
  if aconv encoded `Cexp_num 0` then `Cexp_num 7`
  else
    let head,tail =
      candle_q_dim_stable_program_dest_cval_pair
        "case16594 variable raw list" encoded in
    candle_q_dim_stable_program_cval_pair head
      (candle_disjunctive_case16594_variable_raw_bad_terminator tail);;

let candle_disjunctive_case16594_variable_raw_good_one =
  candle_disjunctive_case16594_variable_raw_result_1.
    variable_raw_encoded_jobs_term;;
let candle_disjunctive_case16594_variable_raw_bad_tail =
  candle_disjunctive_case16594_variable_raw_bad_terminator
    candle_disjunctive_case16594_variable_raw_good_one;;
let candle_disjunctive_case16594_variable_raw_bad_job =
  let _,tail =
    candle_q_dim_stable_program_dest_cval_pair
      "case16594 variable raw first job"
      candle_disjunctive_case16594_variable_raw_good_one in
  candle_q_dim_stable_program_cval_pair `Cexp_num 0` tail;;

let candle_disjunctive_case16594_variable_raw_bad_tail_result =
  candle_disjunctive_case16594_variable_raw_compute
    candle_disjunctive_case16594_variable_raw_bad_tail;;
let candle_disjunctive_case16594_variable_raw_bad_job_result =
  candle_disjunctive_case16594_variable_raw_compute
    candle_disjunctive_case16594_variable_raw_bad_job;;

let candle_disjunctive_case16594_variable_raw_axioms_after = axioms ();;
if not
     (aconv
       (rand
         (concl
           candle_disjunctive_case16594_variable_raw_bad_tail_result))
       `Cexp_num 0`) ||
   not
     (aconv
       (rand
         (concl
           candle_disjunctive_case16594_variable_raw_bad_job_result))
       `Cexp_num 0`) ||
   hyp
     candle_disjunctive_case16594_variable_raw_result_1.
       variable_raw_accept_theorem <> [] ||
   hyp
     candle_disjunctive_case16594_variable_raw_result_8.
       variable_raw_accept_theorem <> [] ||
   hyp
     candle_disjunctive_case16594_variable_raw_result_32.
       variable_raw_accept_theorem <> [] ||
   length candle_disjunctive_case16594_variable_raw_axioms_after <>
     length candle_disjunctive_case16594_variable_raw_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_disjunctive_case16594_variable_raw_axioms_before)
       candle_disjunctive_case16594_variable_raw_axioms_after) then
  failwith "case16594 variable raw batch: final validation failed";;

let candle_disjunctive_case16594_variable_raw_print count result =
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_BATCH_RESULT" ^
     " boxes=" ^ string_of_int count ^
     " theorem_digest=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm result.variable_raw_accept_theorem)));;

let _ =
  candle_disjunctive_case16594_variable_raw_print 1
    candle_disjunctive_case16594_variable_raw_result_1;;
let _ =
  candle_disjunctive_case16594_variable_raw_print 8
    candle_disjunctive_case16594_variable_raw_result_8;;
let _ =
  candle_disjunctive_case16594_variable_raw_print 32
    candle_disjunctive_case16594_variable_raw_result_32;;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_REJECTION_OK cases=2";;
print_endline
  "CANDLE_CV_DISJUNCTIVE_CASE16594_VARIABLE_RAW_BATCH_OK DEVELOPMENT_NON_RELEASE";;

end;;
