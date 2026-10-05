(* Compare proof-producing endpoint normalization with an untrusted, exact   *)
(* data-only decoder.  The fast path is only certificate preparation: final  *)
(* theorem handoff continues to prove the live source-domain correspondence. *)

needs "candle/benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan.ml";;

module Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_bound_decode = struct

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;
open Benchmark_cv_compute_analytic_expr_disjunctive_third_sibling_float_point_plan;;

let candle_disjunctive_data_only_exact_component tm =
  try
    let _ = rat_of_term tm in tm
  with Failure _ ->
    term_of_rat (More_float.num_of_float_tm tm);;

let candle_disjunctive_data_only_normalize_vector vector_tm =
  let vector_head,vector_args = strip_comb vector_tm in
  if fst (dest_const vector_head) <> "vector" || length vector_args <> 1 then
    failwith "data-only bound decoder: expected live explicit vector";
  let components = dest_list (hd vector_args) in
  if length components <> 6 then
    failwith "data-only bound decoder: expected six live coordinates";
  map candle_disjunctive_data_only_exact_component components;;

let candle_disjunctive_data_only_domain_bounds domain_theorem =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_theorem) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  candle_disjunctive_data_only_normalize_vector actual_lower,
  candle_disjunctive_data_only_normalize_vector actual_upper;;

let rec candle_disjunctive_bound_decode_equal_terms left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_bound_decode_equal_terms left_tail right_tail
  | _ -> false;;

let candle_disjunctive_bound_decode_equal (lower1,upper1) (lower2,upper2) =
  candle_disjunctive_bound_decode_equal_terms lower1 lower2 &&
  candle_disjunctive_bound_decode_equal_terms upper1 upper2;;

let rec candle_disjunctive_bound_decode_equal_batches left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      candle_disjunctive_bound_decode_equal left_head right_head &&
      candle_disjunctive_bound_decode_equal_batches left_tail right_tail
  | _ -> false;;

let candle_disjunctive_bound_decode_jobs =
  candle_disjunctive_float_point_sample0 @
  candle_disjunctive_float_point_sample1;;

let _ =
  let axioms_before = axioms () in
  print_endline
    "CANDLE_CV_BOUND_DECODE_PROOF_BEGIN DEVELOPMENT_NON_RELEASE";
  let proved =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_fixed_outer_domain_bounds domain)
      candle_disjunctive_bound_decode_jobs in
  print_endline
    "CANDLE_CV_BOUND_DECODE_PROOF_END DEVELOPMENT_NON_RELEASE";
  print_endline
    "CANDLE_CV_BOUND_DECODE_DATA_BEGIN DEVELOPMENT_NON_RELEASE";
  let decoded =
    map
      (fun (_,_,_,domain) ->
        candle_disjunctive_data_only_domain_bounds domain)
      candle_disjunctive_bound_decode_jobs in
  print_endline
    "CANDLE_CV_BOUND_DECODE_DATA_END DEVELOPMENT_NON_RELEASE";
  let axioms_after = axioms () in
  if length proved <> 1083 || length decoded <> 1083 ||
     not (candle_disjunctive_bound_decode_equal_batches proved decoded) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun axiom -> List.mem axiom axioms_before)
         axioms_after) then
    failwith "data-only bound decoder: validation failed";
  print_endline
    "CANDLE_CV_BOUND_DECODE_OK DEVELOPMENT_NON_RELEASE jobs=1083 endpoints=12996 exact_terms_equal=true assumptions=0 axiom_growth=0";;

end;;
