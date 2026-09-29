(* ========================================================================== *)
(* Batched reflected proof of the first genuine disjunctive-family leaf.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Coarse boxes are split only until their       *)
(* square-root enclosures are positive.  Numerical rejection then refines    *)
(* Taylor cells while retaining one authenticated outer expression and one   *)
(* Kernel.compute call for the complete sibling batch.                        *)
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

type candle_disjunctive_batched_domain_tree =
  | Candle_disjunctive_batched_leaf of thm
  | Candle_disjunctive_batched_glue of
      int * candle_disjunctive_batched_domain_tree *
      candle_disjunctive_batched_domain_tree;;

type candle_disjunctive_batched_result = {
  disjunctive_batched_theorem : thm;
  disjunctive_batched_cells : int;
  disjunctive_batched_outer_groups : int;
  disjunctive_batched_attempts : int;
  disjunctive_batched_max_depth : int;
  disjunctive_batched_group_sizes : int list;
};;

let candle_disjunctive_batched_attempt_counter = ref 0;;

let candle_disjunctive_batched_domain_bounds domain_theorem =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_theorem) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_disjunctive_batched_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_disjunctive_batched_aconv_lists left_tail right_tail
  | _ -> false;;

let rec candle_disjunctive_batched_domains = function
  | Candle_disjunctive_batched_leaf domain -> [domain]
  | Candle_disjunctive_batched_glue (_,left,right) ->
      candle_disjunctive_batched_domains left @
      candle_disjunctive_batched_domains right;;

let rec candle_disjunctive_batched_refine axis = function
  | Candle_disjunctive_batched_leaf domain ->
      let left,right = M_verifier.split_domain 6 6 axis domain in
      Candle_disjunctive_batched_glue
        (axis,Candle_disjunctive_batched_leaf left,
         Candle_disjunctive_batched_leaf right)
  | Candle_disjunctive_batched_glue (old_axis,left,right) ->
      Candle_disjunctive_batched_glue
        (old_axis,
         candle_disjunctive_batched_refine axis left,
         candle_disjunctive_batched_refine axis right);;

let rec candle_disjunctive_batched_glue tree sources =
  match tree with
  | Candle_disjunctive_batched_leaf _ ->
      (match sources with
       | theorem::remaining -> theorem,remaining
       | [] -> failwith "disjunctive batched leaf: missing theorem")
  | Candle_disjunctive_batched_glue (axis,left,right) ->
      let left_theorem,after_left =
        candle_disjunctive_batched_glue left sources in
      let right_theorem,remaining =
        candle_disjunctive_batched_glue right after_left in
      let appended =
        M_verifier.m_glue_cells_list 6 axis left_theorem right_theorem in
      M_verifier.merge_m_cell_list_pass 6 appended,remaining;;

let candle_disjunctive_batched_cell point_plan domain =
  let lower,upper = candle_disjunctive_batched_domain_bounds domain in
  let center_intervals =
    candle_q_dim_taylor_model_point_plan_intervals_six
      point_plan lower upper in
  if length center_intervals <> 10 then
    failwith "disjunctive batched leaf: center slot drift";
  {stable_batch_center_intervals = center_intervals;
   stable_batch_lower = lower;
   stable_batch_upper = upper};;

let rec candle_disjunctive_batched_handoff
    function_term cells sources domains =
  match cells,sources,domains with
  | [],[],[] -> []
  | cell::remaining_cells,source::remaining_sources,
      domain::remaining_domains ->
      let theorem =
        candle_reflected_nl_source_pass_with function_term
          (fun lower upper ->
            if not
                (candle_disjunctive_batched_aconv_lists
                   lower cell.stable_batch_lower &&
                 candle_disjunctive_batched_aconv_lists
                   upper cell.stable_batch_upper) then
              failwith "disjunctive batched leaf: handoff box drift";
            source)
          domain in
      theorem ::
      candle_disjunctive_batched_handoff function_term
        remaining_cells remaining_sources remaining_domains
  | _ -> failwith "disjunctive batched leaf: source cardinality drift";;

let candle_disjunctive_batched_prove_outer
    prepared point_plan outer_depth box_intervals outer_domain =
  let rec prove inner_depth tree =
    let domains = candle_disjunctive_batched_domains tree in
    let cells = map (candle_disjunctive_batched_cell point_plan) domains in
    candle_disjunctive_batched_attempt_counter :=
      !candle_disjunctive_batched_attempt_counter + 1;
    let attempt = !candle_disjunctive_batched_attempt_counter in
    print_endline
      ("CANDLE_CV_DISJUNCTIVE_BATCHED_ATTEMPT" ^
       " attempt=" ^ string_of_int attempt ^
       " outer_depth=" ^ string_of_int outer_depth ^
       " inner_depth=" ^ string_of_int inner_depth ^
       " cells=" ^ string_of_int (length cells) ^ " event=begin");
    try
      let aggregate =
        candle_q_dim_taylor_model_fixed_outer_stable_batch_prove_six
          prepared box_intervals cells in
      let sources =
        candle_q_dim_taylor_model_fixed_outer_stable_batch_cell_sources_six
          aggregate in
      let live =
        candle_disjunctive_batched_handoff
          prepared.function_term cells sources domains in
      let theorem,remaining =
        candle_disjunctive_batched_glue tree live in
      if remaining <> [] then
        failwith "disjunctive batched leaf: trailing theorem";
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_BATCHED_ATTEMPT" ^
         " attempt=" ^ string_of_int attempt ^
         " outer_depth=" ^ string_of_int outer_depth ^
         " inner_depth=" ^ string_of_int inner_depth ^
         " cells=" ^ string_of_int (length cells) ^ " event=accepted");
      {disjunctive_batched_theorem = theorem;
       disjunctive_batched_cells = length cells;
       disjunctive_batched_outer_groups = 1;
       disjunctive_batched_attempts = 1;
       disjunctive_batched_max_depth = outer_depth + inner_depth;
       disjunctive_batched_group_sizes = [length cells]}
    with Failure message ->
      if message <>
           "fixed outer stable Taylor batch prover: numerical batch rejected" ||
         inner_depth > 1 then
        failwith
          ("disjunctive batched leaf: terminal batch failure: " ^ message);
      if inner_depth = 1 then
        failwith "disjunctive batched leaf: tighter outer box required";
      let axis = ((outer_depth + inner_depth) mod 6) + 1 in
      print_endline
        ("CANDLE_CV_DISJUNCTIVE_BATCHED_REFINE" ^
         " attempt=" ^ string_of_int attempt ^
         " outer_depth=" ^ string_of_int outer_depth ^
         " inner_depth=" ^ string_of_int inner_depth ^
         " axis=" ^ string_of_int axis ^
         " cells=" ^ string_of_int (length cells));
      prove (inner_depth + 1)
        (candle_disjunctive_batched_refine axis tree) in
  prove 0 (Candle_disjunctive_batched_leaf outer_domain);;

let candle_disjunctive_batched_append axis left right =
  let appended =
    M_verifier.m_glue_cells_list 6 axis
      left.disjunctive_batched_theorem
      right.disjunctive_batched_theorem in
  {disjunctive_batched_theorem =
     M_verifier.merge_m_cell_list_pass 6 appended;
   disjunctive_batched_cells =
     left.disjunctive_batched_cells + right.disjunctive_batched_cells;
   disjunctive_batched_outer_groups =
     left.disjunctive_batched_outer_groups +
     right.disjunctive_batched_outer_groups;
   disjunctive_batched_attempts =
     left.disjunctive_batched_attempts +
     right.disjunctive_batched_attempts;
   disjunctive_batched_max_depth =
     max left.disjunctive_batched_max_depth
       right.disjunctive_batched_max_depth;
   disjunctive_batched_group_sizes =
     left.disjunctive_batched_group_sizes @
     right.disjunctive_batched_group_sizes};;

let candle_disjunctive_batched_prove
    prepared point_plan maximum_outer_depth domain =
  let rec prove_outer depth domain =
    let lower,upper = candle_disjunctive_batched_domain_bounds domain in
    let prepared_box =
      try
        Some
          (candle_q_box_rational_program_intervals_six
            point_plan.point_plan_programs lower upper)
      with Failure message ->
        if message =
             "analytic box certificate: nonpositive square-root range" then
          None
        else failwith message in
    let split_outer () =
        if depth >= maximum_outer_depth then
          failwith "disjunctive batched leaf: outer preparation depth limit";
        let axis = (depth mod 6) + 1 in
        print_endline
          ("CANDLE_CV_DISJUNCTIVE_BATCHED_OUTER_SPLIT" ^
           " depth=" ^ string_of_int depth ^
           " axis=" ^ string_of_int axis);
        let left_domain,right_domain =
          M_verifier.split_domain 6 6 axis domain in
        candle_disjunctive_batched_append axis
          (prove_outer (depth + 1) left_domain)
          (prove_outer (depth + 1) right_domain) in
    match prepared_box with
    | Some box_intervals ->
        if length box_intervals <> 10 then
          failwith "disjunctive batched leaf: outer slot drift";
        (try
           candle_disjunctive_batched_prove_outer
             prepared point_plan depth box_intervals domain
         with Failure message ->
           if message =
                "disjunctive batched leaf: tighter outer box required" then
             split_outer ()
           else failwith message)
    | None -> split_outer () in
  prove_outer 0 domain;;

let _ =
  let started = Unix.gettimeofday () in
  let axioms_before = axioms () in
  let leaf = List.nth candle_disjunctive_leaf_grouping_leaves 0 in
  let prepared = List.nth candle_disjunctive_plan_prepared 1 in
  if leaf.disjunctive_leaf_function_index <> 1 then
    failwith "disjunctive batched leaf: function selection drift";
  let point_plan = candle_q_dim_taylor_model_point_plan_six prepared in
  if length point_plan.point_plan_programs <> 10 then
    failwith "disjunctive batched leaf: point-plan slot drift";
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      print_endline
        ("CANDLE_CERT_PROFILE lane=disjunctive-first-leaf-batched" ^
         " scope=proof phase=" ^ event));
  candle_disjunctive_batched_attempt_counter := 0;
  let raw_result =
    candle_disjunctive_batched_prove
      prepared point_plan 12 leaf.disjunctive_leaf_domain in
  let result =
    {raw_result with
     disjunctive_batched_attempts =
       !candle_disjunctive_batched_attempt_counter} in
  let functions,proved_domain =
    M_verifier.dest_m_cell_list_pass
      (concl result.disjunctive_batched_theorem) in
  let expected_domain,_,_ =
    M_taylor.dest_m_cell_domain (concl leaf.disjunctive_leaf_domain) in
  let axioms_after = axioms () in
  if functions <> [prepared.function_term] ||
     not (aconv proved_domain expected_domain) ||
     hyp result.disjunctive_batched_theorem <> [] ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before)
         axioms_after) then
    failwith "disjunctive batched leaf: final theorem validation failed";
  let theorem_digest =
    Digest.to_hex
      (Digest.string (string_of_thm result.disjunctive_batched_theorem)) in
  print_endline
    ("CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_BATCHED_RESULT" ^
     " leaf=0 function=1 outer_groups=" ^
     string_of_int result.disjunctive_batched_outer_groups ^
     " batch_attempts=" ^
     string_of_int result.disjunctive_batched_attempts ^
     " cells=" ^ string_of_int result.disjunctive_batched_cells ^
     " max_depth=" ^ string_of_int result.disjunctive_batched_max_depth ^
     " group_sizes=" ^
     String.concat ","
       (map string_of_int result.disjunctive_batched_group_sizes) ^
     " theorem_digest=" ^ theorem_digest ^
     " total_seconds=" ^
     string_of_float (Unix.gettimeofday () -. started));
  print_endline
    "CANDLE_CV_DISJUNCTIVE_FIRST_LEAF_BATCHED_OK DEVELOPMENT_NON_RELEASE";;
