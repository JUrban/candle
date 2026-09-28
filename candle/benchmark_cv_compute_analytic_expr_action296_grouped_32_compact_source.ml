(* ========================================================================== *)
(* Complete compact-tree handoff on the authentic first 32 action-296 roots. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The cached fixed-algebraic batch results and  *)
(* logical trees are unchanged.  Each compact result is checked against the  *)
(* independently constructed recursive-tree theorem from the baseline run.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_taylor_model_tree_compact_prove.ml";;
needs "candle/test_cv_compute_analytic_expr_action296_grouped_32_adaptive_proof.ml";;

open Candle_cv_analytic_expr_taylor_model_tree_compact_prove;;

let candle_action296_grouped_32_compact_source_axioms_before = axioms ();;

let candle_action296_grouped_32_compact_source_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-compact-source" ^
     " scope=first-32 phase=" ^ phase ^ " event=" ^ event);;

let rec candle_action296_grouped_32_compact_source_project_trees
    result remaining_jobs remaining_accept = function
  | [] -> [],remaining_jobs,remaining_accept
  | (index,logical) :: remaining_trees ->
      let phase = "root-" ^ string_of_int index in
      let _ =
        candle_action296_grouped_32_compact_source_marker phase "begin" in
      let jobs_call =
        mk_comb
          (`candle_q_dim_taylor_model_tree_jobs`,
           logical.grouped_32_proof_logical_term) in
      let jobs_expansion =
        REWRITE_CONV
          [candle_q_dim_taylor_model_tree_jobs_def;APPEND]
          jobs_call in
      let tree_jobs = rand (concl jobs_expansion) in
      let tree_items = dest_list tree_jobs and
          remaining_items = dest_list remaining_jobs in
      let tree_count = length tree_items in
      if tree_count = 0 || tree_count > length remaining_items ||
         not
           (candle_action296_grouped_32_proof_aconv_lists
             tree_items (fst (chop_list tree_count remaining_items))) then
        failwith "action296 compact source: non-prefix tree jobs";
      let _,suffix_items = chop_list tree_count remaining_items in
      let job_type = type_of (hd remaining_items) in
      let suffix_jobs = mk_list (suffix_items,job_type) in
      let append_call =
        list_mk_comb
          (candle_action296_grouped_32_proof_append_function,
           [tree_jobs;suffix_jobs]) in
      let append_expansion = REWRITE_CONV [APPEND] append_call in
      if hyp append_expansion <> [] ||
         not (aconv (rand (concl append_expansion)) remaining_jobs) then
        failwith "action296 compact source: append expansion mismatch";
      let split_accept =
        REWRITE_RULE
          [candle_q_dim_taylor_model_fixed_algebraic_batch_accept_append]
          (REWRITE_RULE [SYM append_expansion] remaining_accept) in
      let tree_accept,suffix_accept =
        if suffix_items = [] then begin
          if remaining_trees <> [] || not (aconv tree_jobs remaining_jobs) then
            failwith "action296 compact source: malformed terminal tree";
          remaining_accept,remaining_accept
        end else
          CONJ_PAIR split_accept in
      let narrowed =
        candle_action296_grouped_32_proof_narrow_result
          result tree_accept tree_jobs in
      candle_q_dim_taylor_model_tree_compact_prove_profile :=
        (fun event ->
          print_endline
            ("CANDLE_COMPACT_SOURCE_STEP root=" ^ string_of_int index ^
             " event=" ^ event));
      let source =
        candle_q_dim_taylor_model_fixed_algebraic_tree_compact_source_six
          narrowed logical.grouped_32_proof_logical_term in
      let live =
        candle_action296_grouped_32_proof_root_live source logical in
      let baseline =
        try assoc index (candle_action296_grouped_32_proof_leaf_results ())
        with Not_found ->
          failwith "action296 compact source: missing baseline theorem" in
      if hyp live <> [] || not (aconv (concl live) (concl baseline)) then
        failwith "action296 compact source: theorem mismatch";
      let _ =
        candle_action296_grouped_32_compact_source_marker phase "end" in
      let projected,final_jobs,final_accept =
        candle_action296_grouped_32_compact_source_project_trees
          result suffix_jobs suffix_accept remaining_trees in
      (index,live) :: projected,final_jobs,final_accept;;

let candle_action296_grouped_32_compact_source_project_group
    result logical_trees =
  let projected,remaining_jobs,_ =
    candle_action296_grouped_32_compact_source_project_trees
      result result.fixed_algebraic_batch_jobs_term
      result.fixed_algebraic_batch_accept_theorem logical_trees in
  if dest_list remaining_jobs <> [] then
    failwith "action296 compact source: unconsumed aggregate jobs";
  projected;;

let _ =
  candle_action296_grouped_32_compact_source_marker
    "compact-root-handoffs" "begin";;
let candle_action296_grouped_32_compact_source_results =
  List.flatten
    (candle_action296_grouped_32_split_scan_map2
      candle_action296_grouped_32_compact_source_project_group
      (candle_action296_grouped_32_proof_results ())
      (candle_action296_grouped_32_proof_logical_groups ()));;
let _ =
  candle_action296_grouped_32_compact_source_marker
    "compact-root-handoffs" "end";;

let candle_action296_grouped_32_compact_source_axioms_after = axioms ();;
let candle_action296_grouped_32_compact_source_digest =
  Digest.to_hex
    (Digest.string
      (String.concat "\n"
        (map
          (fun (_,theorem) -> string_of_thm theorem)
          candle_action296_grouped_32_compact_source_results)));;

if length candle_action296_grouped_32_compact_source_results <> 32 ||
   candle_action296_grouped_32_compact_source_digest <>
     candle_action296_grouped_32_proof_digest ||
   length candle_action296_grouped_32_compact_source_axioms_after <>
     length candle_action296_grouped_32_compact_source_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_grouped_32_compact_source_axioms_before)
       candle_action296_grouped_32_compact_source_axioms_after) then
  failwith "action296 compact source: final validation";;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_COMPACT_SOURCE_RESULT roots=32" ^
   " theorem_digest=" ^
   candle_action296_grouped_32_compact_source_digest);;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_COMPACT_SOURCE_OK DEVELOPMENT_NON_RELEASE";;
