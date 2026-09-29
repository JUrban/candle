(* ========================================================================== *)
(* Focused exact-box subdivision test for the hard depth-12 box of leaf 394. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Recurse only within this isolated box, with  *)
(* a strict depth-18 cap, then validate the glued exact parent theorem.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

let candle_disjunctive_leaf394_depth13_path =
  [false;false;false;false;false;false;false;true;
   false;false;true;false];;

let rec candle_disjunctive_leaf394_depth13_follow depth domain = function
  | [] -> domain
  | choose_right :: remaining ->
      let axis = (depth mod 6) + 1 in
      let left,right = M_verifier.split_domain 6 6 axis domain in
      candle_disjunctive_leaf394_depth13_follow (depth + 1)
        (if choose_right then right else left) remaining;;

type candle_disjunctive_leaf394_exact_result = {
  leaf394_exact_theorem : thm;
  leaf394_exact_cells : int;
  leaf394_exact_max_depth : int;
};;

let candle_disjunctive_leaf394_exact_attempts = ref 0;;

let rec candle_disjunctive_leaf394_exact_prove
    prepared point_plan depth domain =
  candle_disjunctive_leaf394_exact_attempts :=
    !candle_disjunctive_leaf394_exact_attempts + 1;
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_ATTEMPT" ^
     " attempt=" ^ string_of_int !candle_disjunctive_leaf394_exact_attempts ^
     " depth=" ^ string_of_int depth ^ " event=begin");
  try
    let theorem =
      candle_disjunctive_fixed_outer_exact_box_attempt
        prepared point_plan domain in
    print_endline
      ("CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_ATTEMPT" ^
       " attempt=" ^ string_of_int !candle_disjunctive_leaf394_exact_attempts ^
       " depth=" ^ string_of_int depth ^ " event=accepted");
    {leaf394_exact_theorem = theorem;
     leaf394_exact_cells = 1;
     leaf394_exact_max_depth = depth}
  with Failure message ->
    if message <>
         "fixed outer stable Taylor batch prover: numerical batch rejected" ||
       depth >= 18 then
      failwith
        ("disjunctive leaf394 exact recursion: terminal failure: " ^ message);
    let axis = (depth mod 6) + 1 in
    let left_domain,right_domain = M_verifier.split_domain 6 6 axis domain in
    let left =
      candle_disjunctive_leaf394_exact_prove
        prepared point_plan (depth + 1) left_domain in
    let right =
      candle_disjunctive_leaf394_exact_prove
        prepared point_plan (depth + 1) right_domain in
    let theorem =
      M_verifier.merge_m_cell_list_pass 6
        (M_verifier.m_glue_cells_list 6 axis
          left.leaf394_exact_theorem right.leaf394_exact_theorem) in
    {leaf394_exact_theorem = theorem;
     leaf394_exact_cells =
       left.leaf394_exact_cells + right.leaf394_exact_cells;
     leaf394_exact_max_depth =
       max left.leaf394_exact_max_depth right.leaf394_exact_max_depth};;

let _ =
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves 394 in
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  let point_plan =
    Candle_cv_analytic_expr_certificate_variant_prepare.
      candle_q_dim_taylor_model_point_plan_six prepared in
  let parent =
    candle_disjunctive_leaf394_depth13_follow
      0 leaf.disjunctive_leaf_domain
      candle_disjunctive_leaf394_depth13_path in
  let result =
    candle_disjunctive_leaf394_exact_prove
      prepared point_plan 12 parent in
  let theorem = result.leaf394_exact_theorem in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass (concl theorem) in
  let expected_domain,_,_ = M_taylor.dest_m_cell_domain (concl parent) in
  if functions <>
       [candle_disjunctive_fixed_outer_function_term prepared] ||
     not (aconv proved_domain expected_domain) || hyp theorem <> [] then
    failwith "disjunctive leaf394 depth13: parent theorem mismatch";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_LEAF394_DEPTH13_RESULT" ^
     " attempts=" ^
     string_of_int !candle_disjunctive_leaf394_exact_attempts ^
     " cells=" ^ string_of_int result.leaf394_exact_cells ^
     " max_depth=" ^ string_of_int result.leaf394_exact_max_depth ^
     " outer_proposal=exact-box theorem_digest=" ^
     Digest.to_hex (Digest.string (string_of_thm theorem)));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_LEAF394_DEPTH13_OK DEVELOPMENT_NON_RELEASE";;
