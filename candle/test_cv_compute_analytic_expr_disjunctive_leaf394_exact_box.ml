(* ========================================================================== *)
(* Focused exact-interval proposal for the hard depth-12 subbox of leaf 394. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Exact rational interval evaluation supplies  *)
(* the square-root enclosures.  The complete reflected checker authenticates *)
(* them and is solely responsible for producing any theorem.                 *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_disjunctive_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_disjunctive_fixed_outer_prove.ml";;

open Candle_cv_analytic_expr_disjunctive_plan;;
open Candle_cv_analytic_expr_disjunctive_leaf_grouping_fixture;;
open Candle_cv_analytic_expr_disjunctive_fixed_outer_prove;;

let candle_disjunctive_leaf394_exact_box_path =
  [false;false;false;false;false;false;false;true;
   false;false;true;false];;

let rec candle_disjunctive_leaf394_exact_box_follow depth domain = function
  | [] -> domain
  | choose_right :: remaining ->
      let axis = (depth mod 6) + 1 in
      let left,right = M_verifier.split_domain 6 6 axis domain in
      candle_disjunctive_leaf394_exact_box_follow (depth + 1)
        (if choose_right then right else left) remaining;;

let _ =
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves 394 in
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  let point_plan =
    Candle_cv_analytic_expr_certificate_variant_prepare.
      candle_q_dim_taylor_model_point_plan_six prepared in
  let domain =
    candle_disjunctive_leaf394_exact_box_follow
      0 leaf.disjunctive_leaf_domain
      candle_disjunctive_leaf394_exact_box_path in
  print_endline
    "CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_ATTEMPT event=begin";
  let theorem =
    candle_disjunctive_fixed_outer_exact_box_attempt
      prepared point_plan domain in
  if hyp theorem <> [] then
    failwith "disjunctive leaf394 exact box: theorem assumptions";
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_RESULT" ^
     " depth=12 theorem_digest=" ^
     Digest.to_hex (Digest.string (string_of_thm theorem)));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_LEAF394_EXACT_BOX_OK DEVELOPMENT_NON_RELEASE";;
