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

open Certificate;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove;;

type candle_disjunctive_first_leaf_result = {
  disjunctive_first_leaf_theorem : thm;
  disjunctive_first_leaf_cells : int;
  disjunctive_first_leaf_max_depth : int;
};;

let candle_disjunctive_first_leaf_domain_bounds domain_theorem =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_theorem) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_disjunctive_first_leaf_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_first_leaf_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_first_leaf_retryable = function
  | "analytic box certificate: nonpositive square-root range"
  | "fixed outer stable Taylor batch prover: numerical batch rejected" -> true
  | _ -> false;;

let candle_disjunctive_first_leaf_attempt
    prepared point_plan domain =
  let lower,upper =
    candle_disjunctive_first_leaf_domain_bounds domain in
  let box_intervals =
    candle_q_box_rational_program_intervals_six
      point_plan.point_plan_programs lower upper in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  if length box_intervals <> 10 || length center_intervals <> 10 then
    failwith "disjunctive first leaf: square-root slot drift";
  let cell =
    {stable_batch_center_intervals = center_intervals;
     stable_batch_lower = lower;
     stable_batch_upper = upper} in
  let aggregate =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
      prepared box_intervals [cell] in
  let source =
    candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_source_six
      aggregate cell in
  candle_reflected_nl_source_pass_with prepared.function_term
    (fun actual_lower actual_upper ->
      if not
          (candle_disjunctive_first_leaf_aconv_lists
             actual_lower lower &&
           candle_disjunctive_first_leaf_aconv_lists
             actual_upper upper) then
        failwith "disjunctive first leaf: unexpected handoff box";
      source)
    domain;;

let candle_disjunctive_first_leaf_prove
    prepared point_plan attempts maximum_depth domain =
  let rec prove depth domain =
    attempts := !attempts + 1;
    print_endline
      ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_ATTEMPT" ^
       " attempt=" ^ string_of_int !attempts ^
       " depth=" ^ string_of_int depth ^ " event=begin");
    try
      let theorem =
        candle_disjunctive_first_leaf_attempt prepared point_plan domain in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_ATTEMPT" ^
         " attempt=" ^ string_of_int !attempts ^
         " depth=" ^ string_of_int depth ^ " event=accepted");
      {disjunctive_first_leaf_theorem = theorem;
       disjunctive_first_leaf_cells = 1;
       disjunctive_first_leaf_max_depth = depth}
    with Failure message ->
      if depth >= maximum_depth ||
         not (candle_disjunctive_first_leaf_retryable message) then
        failwith
          ("disjunctive first leaf: terminal attempt failure: " ^ message);
      let axis = (depth mod 6) + 1 in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_SPLIT" ^
         " attempt=" ^ string_of_int !attempts ^
         " depth=" ^ string_of_int depth ^
         " axis=" ^ string_of_int axis ^
         " reason=" ^ message);
      let left_domain,right_domain =
        M_verifier.split_domain 6 6 axis domain in
      let left = prove (depth + 1) left_domain in
      let right = prove (depth + 1) right_domain in
      let appended =
        M_verifier.m_glue_cells_list 6 axis
          left.disjunctive_first_leaf_theorem
          right.disjunctive_first_leaf_theorem in
      {disjunctive_first_leaf_theorem =
         M_verifier.merge_m_cell_list_pass 6 appended;
       disjunctive_first_leaf_cells =
         left.disjunctive_first_leaf_cells +
         right.disjunctive_first_leaf_cells;
       disjunctive_first_leaf_max_depth =
         max left.disjunctive_first_leaf_max_depth
           right.disjunctive_first_leaf_max_depth} in
  prove 0 domain;;

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
  if length point_plan.point_plan_programs <> 10 then
    failwith "disjunctive first leaf: point-plan slot drift";
  let attempts = ref 0 in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-first-leaf" ^
         " scope=proof phase=" ^ event));
  let result =
    candle_disjunctive_first_leaf_prove
      prepared point_plan attempts 12 leaf.disjunctive_leaf_domain in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_first_leaf_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  let axioms_after = axioms () in
  if functions <> [prepared.function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_first_leaf_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "disjunctive first leaf: final theorem validation failed";
  let theorem_digest =
    Digest.to_hex
      (Digest.string
        (string_of_thm result.disjunctive_first_leaf_theorem)) in
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_RESULT" ^
     " leaf=0 function=1 attempts=" ^ string_of_int !attempts ^
     " cells=" ^ string_of_int result.disjunctive_first_leaf_cells ^
     " max_depth=" ^
     string_of_int result.disjunctive_first_leaf_max_depth ^
     " sqrt_slots=10 theorem_digest=" ^ theorem_digest ^
     " total_seconds=" ^
     string_of_float (Unix.gettimeofday () -. started));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_OK DEVELOPMENT_NON_RELEASE";;
