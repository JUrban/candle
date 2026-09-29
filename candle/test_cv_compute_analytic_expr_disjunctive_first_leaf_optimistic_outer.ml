(* ========================================================================== *)
(* Discriminating test for optimistic whole-box square-root preparation.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Exact center certificates are widened by a   *)
(* bounded sequence of rational factors.  This preparation is deliberately  *)
(* untrusted: only the reflected checker can accept a candidate and produce  *)
(* the exact ordinary leaf theorem.                                           *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml";;

open Candle_cv_exact_interval_reify;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_stable_batch_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove;;

let candle_disjunctive_optimistic_domain_bounds domain_theorem =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_theorem) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_disjunctive_optimistic_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_optimistic_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_disjunctive_optimistic_q_num value =
  let signed,denominator_predecessor = dest_pair value in
  let positive,negative = dest_pair signed in
  Num.div_num
    (Num.sub_num (dest_numeral positive) (dest_numeral negative))
    (Num.add_num
      (dest_numeral denominator_predecessor) (Num.num_of_int 1));;

let candle_disjunctive_optimistic_widen numerator denominator interval =
  let lower,upper = dest_pair interval in
  let factor =
    Num.div_num (Num.num_of_int numerator) (Num.num_of_int denominator) in
  mk_pair
    (candle_q_term
      (Num.div_num (candle_disjunctive_optimistic_q_num lower) factor),
     candle_q_term
      (Num.mul_num (candle_disjunctive_optimistic_q_num upper) factor));;

let candle_disjunctive_optimistic_factors =
  [(1001,1000);(101,100);(21,20);(11,10);
   (5,4);(3,2);(2,1);(4,1)];;

let candle_disjunctive_optimistic_attempt
    prepared point_plan domain numerator denominator =
  let lower,upper = candle_disjunctive_optimistic_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  let box_intervals =
    map (candle_disjunctive_optimistic_widen numerator denominator)
      center_intervals in
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
          (candle_disjunctive_optimistic_aconv_lists actual_lower lower &&
           candle_disjunctive_optimistic_aconv_lists actual_upper upper) then
        failwith "disjunctive optimistic outer: handoff box drift";
      source)
    domain;;

let rec candle_disjunctive_optimistic_search
    prepared point_plan domain attempts = function
  | [] -> failwith "disjunctive optimistic outer: no factor accepted"
  | (numerator,denominator) :: remaining ->
      attempts := !attempts + 1;
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_ATTEMPT" ^
         " attempt=" ^ string_of_int !attempts ^
         " factor=" ^ string_of_int numerator ^ "/" ^
         string_of_int denominator ^ " event=begin");
      try
        let theorem =
          candle_disjunctive_optimistic_attempt
            prepared point_plan domain numerator denominator in
        print_endline
          ("CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_ATTEMPT" ^
           " attempt=" ^ string_of_int !attempts ^
           " factor=" ^ string_of_int numerator ^ "/" ^
           string_of_int denominator ^ " event=accepted");
        numerator,denominator,theorem
      with Failure message ->
        if message <>
             "fixed outer stable Taylor batch prover: numerical batch rejected"
        then failwith message;
        print_endline
          ("CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_ATTEMPT" ^
           " attempt=" ^ string_of_int !attempts ^
           " factor=" ^ string_of_int numerator ^ "/" ^
           string_of_int denominator ^ " event=rejected");
        candle_disjunctive_optimistic_search
          prepared point_plan domain attempts remaining;;

let _ =
  let axioms_before = axioms () in
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves 0 in
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  let point_plan = candle_q_dim_taylor_model_point_plan_six prepared in
  let attempts = ref 0 in
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-optimistic-outer" ^
         " scope=proof phase=" ^ event));
  let numerator,denominator,theorem =
    candle_disjunctive_optimistic_search
      prepared point_plan leaf.disjunctive_leaf_domain attempts
      candle_disjunctive_optimistic_factors in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  let axioms_after = axioms () in
  if functions <> [prepared.function_term] ||
     not (aconv proved_domain expected_domain) || hyp theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "disjunctive optimistic outer: final theorem validation failed";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_RESULT" ^
     " leaf=0 function=1 attempts=" ^ string_of_int !attempts ^
     " factor=" ^ string_of_int numerator ^ "/" ^
     string_of_int denominator ^
     " cells=1 theorem_digest=" ^
     Digest.to_hex (Digest.string (string_of_thm theorem)));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_OPTIMISTIC_OK DEVELOPMENT_NON_RELEASE";;
