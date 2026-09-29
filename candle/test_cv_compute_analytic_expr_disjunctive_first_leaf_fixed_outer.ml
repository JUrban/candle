(* ========================================================================== *)
(* Complete reflected proof of the first genuine disjunctive-family leaf.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The exact ordinary-verifier leaf is attempted *)
(* first.  Only a loose whole-box square-root enclosure or a negative         *)
(* reflected verdict may trigger bounded round-robin subdivision.  Every     *)
(* accepted child is proved independently and glued back to the original     *)
(* authenticated leaf.                                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

let _ =
  let started = Unix.gettimeofday () in
  let axioms_before = axioms () in
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves 0 in
  if leaf.disjunctive_leaf_function_index <> 1 then
    failwith "disjunctive first leaf: function selection drift";
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  let acs_slots =
    candle_analytic_collect_sqrt_intervals
      (fun square_root -> square_root) [] `acs (&1 / &3)` in
  if length acs_slots <> 1 ||
     candle_analytic_collect_sqrt_intervals
       (fun square_root -> square_root) [] `pi` <> [] then
    failwith "disjunctive first leaf: derived certificate-slot drift";
  let point_plan = candle_q_dim_taylor_model_point_plan_six prepared in
  if length point_plan.point_plan_programs <> 10 ||
     candle_disjunctive_fixed_outer_widen_numerator <> 5 ||
     candle_disjunctive_fixed_outer_widen_denominator <> 4 then
    failwith "disjunctive first leaf: point-plan slot drift";
  let attempts = ref 0 in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-first-leaf" ^
         " scope=proof phase=" ^ event));
  let result =
    candle_disjunctive_fixed_outer_prove
      prepared point_plan "leaf-0" attempts 12
      leaf.disjunctive_leaf_domain in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_fixed_outer_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  let axioms_after = axioms () in
  if functions <> [prepared.function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_fixed_outer_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "disjunctive first leaf: final theorem validation failed";
  let theorem_digest =
    Digest.to_hex
      (Digest.string
        (string_of_thm result.disjunctive_fixed_outer_theorem)) in
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_RESULT" ^
     " leaf=0 function=1 attempts=" ^ string_of_int !attempts ^
     " cells=" ^ string_of_int result.disjunctive_fixed_outer_cells ^
     " max_depth=" ^
     string_of_int result.disjunctive_fixed_outer_max_depth ^
     " sqrt_slots=10 outer_factor=5/4 theorem_digest=" ^ theorem_digest ^
     " total_seconds=" ^
     string_of_float (Unix.gettimeofday () -. started));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_OK DEVELOPMENT_NON_RELEASE";;
