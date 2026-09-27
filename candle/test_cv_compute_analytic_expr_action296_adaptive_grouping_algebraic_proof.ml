(* ========================================================================== *)
(* Proof-producing adaptive batch over the first eight genuine NL leaves.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The first four leaves are split once on axis  *)
(* four, while the next four remain whole.  The twelve final cells use two   *)
(* shared source preparations and two compact aggregate evaluator verdicts.   *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_adaptive_grouping_algebraic.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_batch_prove;;

let candle_action296_adaptive_proof_axioms_before = axioms ();;

let candle_action296_adaptive_proof_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-adaptive-grouping-proof" ^
     " scope=first-8 phase=" ^ phase ^ " event=" ^ event);;

let rec candle_action296_adaptive_proof_aconv_lists left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      aconv left_head right_head &&
      candle_action296_adaptive_proof_aconv_lists left_tail right_tail
  | _ -> false;;

let candle_action296_adaptive_proof_cell prepared plan domain_th =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain_th in
  {
    fixed_algebraic_batch_center_variant =
      candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
        prepared plan lower upper;
    fixed_algebraic_batch_lower = lower;
    fixed_algebraic_batch_upper = upper;
  };;

let _ =
  candle_action296_adaptive_proof_marker "cell-preparation" "begin";;
let candle_action296_adaptive_proof_cells_ref :
    candle_q_dim_taylor_model_fixed_algebraic_batch_cell_six list list option ref =
  ref None;;
let _ =
  candle_action296_adaptive_proof_cells_ref :=
    Some
      (candle_action296_adaptive_grouping_map3
        (fun prepared plan domains ->
          map (candle_action296_adaptive_proof_cell prepared plan) domains)
        (candle_action296_adaptive_grouping_prepared ())
        (candle_action296_adaptive_grouping_plans ())
        candle_action296_adaptive_grouping_finals);;
let _ =
  candle_action296_adaptive_proof_marker "cell-preparation" "end";;

let candle_action296_adaptive_proof_cells () =
  match !candle_action296_adaptive_proof_cells_ref with
  | Some cells -> cells
  | None -> failwith "action296 adaptive proof: missing cells";;

let _ =
  candle_action296_adaptive_proof_marker "aggregate-proofs" "begin";;
let candle_action296_adaptive_proof_results_ref :
    candle_q_dim_taylor_model_fixed_algebraic_batch_result_six list option ref =
  ref None;;
let _ =
  candle_action296_adaptive_proof_results_ref :=
    Some
      (map2 candle_q_dim_taylor_model_fixed_algebraic_batch_prove_six
        (candle_action296_adaptive_grouping_prepared ())
        (candle_action296_adaptive_proof_cells ()));;
let _ =
  candle_action296_adaptive_proof_marker "aggregate-proofs" "end";;

let candle_action296_adaptive_proof_results () =
  match !candle_action296_adaptive_proof_results_ref with
  | Some results -> results
  | None -> failwith "action296 adaptive proof: missing aggregate results";;

let _ =
  candle_action296_adaptive_proof_marker "source-extraction" "begin";;
let candle_action296_adaptive_proof_sources_ref : thm list option ref =
  ref None;;
let _ =
  candle_action296_adaptive_proof_sources_ref :=
    Some
      (List.flatten
        (map2
          (fun result cells ->
            map
              (candle_q_dim_taylor_model_fixed_algebraic_batch_cell_source_six
                result)
              cells)
          (candle_action296_adaptive_proof_results ())
          (candle_action296_adaptive_proof_cells ())));;
let _ =
  candle_action296_adaptive_proof_marker "source-extraction" "end";;

let candle_action296_adaptive_proof_sources () =
  match !candle_action296_adaptive_proof_sources_ref with
  | Some sources -> sources
  | None -> failwith "action296 adaptive proof: missing sources";;

let candle_action296_adaptive_proof_live cell source domain_th =
  candle_reflected_nl_source_pass_with
    candle_action296_plan_prepared.function_term
    (fun lower upper ->
      if not
          (candle_action296_adaptive_proof_aconv_lists
             lower cell.fixed_algebraic_batch_lower &&
           candle_action296_adaptive_proof_aconv_lists
             upper cell.fixed_algebraic_batch_upper) then
        failwith "action296 adaptive proof: unexpected handoff box";
      source)
    domain_th;;

let rec candle_action296_adaptive_proof_map3 action left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head::left_tail,middle_head::middle_tail,right_head::right_tail ->
      action left_head middle_head right_head ::
      candle_action296_adaptive_proof_map3
        action left_tail middle_tail right_tail
  | _ -> failwith "action296 adaptive proof: live cardinality";;

let candle_action296_adaptive_proof_source_groups_ref :
    thm list list option ref = ref None;;
let _ =
  candle_action296_adaptive_proof_source_groups_ref :=
    Some
      (match candle_action296_adaptive_proof_cells () with
       | [first_cells;second_cells] ->
           let first_length = length first_cells in
           let first_sources,second_sources =
             chop_list first_length
               (candle_action296_adaptive_proof_sources ()) in
           [first_sources;second_sources]
       | _ -> failwith "action296 adaptive proof: source group shape");;

let candle_action296_adaptive_proof_source_groups () =
  match !candle_action296_adaptive_proof_source_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 adaptive proof: missing source groups";;

let _ =
  candle_action296_adaptive_proof_marker "live-handoff" "begin";;
let candle_action296_adaptive_proof_live_groups_ref :
    thm list list option ref = ref None;;
let _ =
  candle_action296_adaptive_proof_live_groups_ref :=
    Some
      (candle_action296_adaptive_proof_map3
        (fun cells sources domains ->
          candle_action296_adaptive_proof_map3
            candle_action296_adaptive_proof_live cells sources domains)
        (candle_action296_adaptive_proof_cells ())
        (candle_action296_adaptive_proof_source_groups ())
        candle_action296_adaptive_grouping_finals);;
let _ =
  candle_action296_adaptive_proof_marker "live-handoff" "end";;

let candle_action296_adaptive_proof_live_groups () =
  match !candle_action296_adaptive_proof_live_groups_ref with
  | Some groups -> groups
  | None -> failwith "action296 adaptive proof: missing live groups";;

let rec candle_action296_adaptive_proof_glue_pairs = function
  | [] -> []
  | left::right::tail ->
      M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
        (M_verifier.m_glue_cells_list
          candle_action296_plan_dimension 4 left right) ::
      candle_action296_adaptive_proof_glue_pairs tail
  | _ -> failwith "action296 adaptive proof: unpaired child";;

let candle_action296_adaptive_proof_leaf_theorems_ref :
    thm list option ref = ref None;;
let _ =
  candle_action296_adaptive_proof_leaf_theorems_ref :=
    Some
      (match candle_action296_adaptive_proof_live_groups () with
       | [split_children;unsplit_leaves] ->
           candle_action296_adaptive_proof_glue_pairs split_children @
           unsplit_leaves
       | _ -> failwith "action296 adaptive proof: live group shape");;

let candle_action296_adaptive_proof_leaf_theorems () =
  match !candle_action296_adaptive_proof_leaf_theorems_ref with
  | Some theorems -> theorems
  | None -> failwith "action296 adaptive proof: missing leaf theorems";;

let candle_action296_adaptive_proof_result_shape theorem =
  let functions,domain =
    M_verifier.dest_m_cell_list_pass (concl theorem) in
  functions,domain;;

let candle_action296_adaptive_proof_expected_domain domain_th =
  let domain,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  domain;;

let rec candle_action296_adaptive_proof_for_all2 predicate left right =
  match left,right with
  | [],[] -> true
  | left_head::left_tail,right_head::right_tail ->
      predicate left_head right_head &&
      candle_action296_adaptive_proof_for_all2 predicate left_tail right_tail
  | _ -> false;;

let candle_action296_adaptive_proof_valid =
  length (candle_action296_adaptive_proof_sources ()) = 12 &&
  length (candle_action296_adaptive_proof_leaf_theorems ()) = 8 &&
  List.for_all (fun theorem -> hyp theorem = [])
    (candle_action296_adaptive_proof_sources ()) &&
  candle_action296_adaptive_proof_for_all2
    (fun theorem expected_domain ->
      let functions,proved_domain =
        candle_action296_adaptive_proof_result_shape theorem in
      functions = [candle_action296_plan_prepared.function_term] &&
      aconv proved_domain
        (candle_action296_adaptive_proof_expected_domain expected_domain) &&
      hyp theorem = [])
    (candle_action296_adaptive_proof_leaf_theorems ())
    candle_action296_leaf_grouping_domains;;

let candle_action296_adaptive_proof_digest =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map string_of_thm
          (candle_action296_adaptive_proof_leaf_theorems ()))));;

let candle_action296_adaptive_proof_axioms_after = axioms ();;

if not candle_action296_adaptive_proof_valid ||
   candle_action296_adaptive_proof_digest <>
     "7cf22acbe5ab0f7bce693d199f91dbe7" ||
   length candle_action296_adaptive_proof_axioms_after <>
     length candle_action296_adaptive_proof_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_adaptive_proof_axioms_before)
       candle_action296_adaptive_proof_axioms_after) then
  failwith "action296 adaptive proof: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_ADAPTIVE_GROUPING_PROOF_RESULT" ^
   " original_leaves=8 final_cells=12 shared_preparations=2" ^
   " computes=2 theorem_digest=" ^
   candle_action296_adaptive_proof_digest);;
print_endline
  "CANDLE_CV_ACTION296_ADAPTIVE_GROUPING_PROOF_OK DEVELOPMENT_NON_RELEASE";;
