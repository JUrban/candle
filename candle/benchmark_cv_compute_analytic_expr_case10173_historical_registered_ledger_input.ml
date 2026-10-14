(* ========================================================================== *)
(* Exact Candle-side input for the balanced case-10173 registration ledger. *)
(*                                                                            *)
(* This rebuilds the same 261 aligned calls and the same two-level balanced  *)
(* padding shape emitted to HOL4.  It also provides the one-time structural  *)
(* guard preparation used by the source-level registered-result combiner.    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_historical_registered_input.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_registered_combine.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_ledger_input = struct

open Benchmark_cv_compute_analytic_expr_case10173_historical_registered_input;;
open Candle_cv_analytic_expr_case10173_historical_authenticated_batch_sound;;
open Candle_cv_analytic_expr_case10173_historical_registered_combine;;

type candle_case10173_historical_registered_chunk = {
  registered_chunk_start : int;
  registered_chunk_count : int;
  registered_chunk_encoded_jobs : term;
  registered_chunk_roots : term;
  registered_chunk_call : term;
};;

type candle_case10173_historical_registered_ledger_input = {
  registered_ledger_chunks :
    candle_case10173_historical_registered_chunk list;
  registered_ledger_full_encoded_jobs : term;
  registered_ledger_call : term;
  registered_ledger_expected_result : term;
};;

let rec candle_case10173_registered_take count items =
  if count = 0 then []
  else match items with
  | [] -> failwith "case10173 registered ledger input: short list"
  | item :: remaining ->
      item :: candle_case10173_registered_take (count - 1) remaining;;

let rec candle_case10173_registered_drop count items =
  if count = 0 then items
  else match items with
  | [] -> failwith "case10173 registered ledger input: short list"
  | _ :: remaining ->
      candle_case10173_registered_drop (count - 1) remaining;;

let rec candle_case10173_registered_repeat count item =
  if count = 0 then []
  else item :: candle_case10173_registered_repeat (count - 1) item;;

let candle_case10173_registered_pad size filler items =
  let count = length items in
  if count > size then
    failwith "case10173 registered ledger input: padding overflow";
  items @ candle_case10173_registered_repeat (size - count) filler;;

let rec candle_case10173_registered_pair_tree = function
  | [] -> failwith "case10173 registered ledger input: empty pair tree"
  | [item] -> item
  | items ->
      let count = length items in
      if count mod 2 <> 0 then
        failwith "case10173 registered ledger input: unbalanced pair tree";
      let half = count / 2 in
      list_mk_comb
        (`Cexp_pair`,
         [candle_case10173_registered_pair_tree
            (candle_case10173_registered_take half items);
          candle_case10173_registered_pair_tree
            (candle_case10173_registered_drop half items)]);;

let rec candle_case10173_registered_groups group_size = function
  | [] -> []
  | items ->
      let count = min group_size (length items) in
      candle_case10173_registered_take count items ::
      candle_case10173_registered_groups group_size
        (candle_case10173_registered_drop count items);;

let rec candle_case10173_registered_for_all2 predicate left right =
  match left,right with
  | [],[] -> true
  | left_head :: left_tail,right_head :: right_tail ->
      predicate left_head right_head &&
      candle_case10173_registered_for_all2 predicate left_tail right_tail
  | _ -> false;;

let candle_case10173_historical_registered_ledger_input () =
  let input = candle_case10173_historical_registered_input () in
  let full_call = input.registered_input_checked_call in
  let operator,arguments = strip_comb full_call in
  let source_program,encoded_jobs,roots =
    match arguments with
    | [source_program;encoded_jobs;roots] ->
        source_program,encoded_jobs,roots
    | _ -> failwith "case10173 registered ledger input: malformed full call" in
  let rec chunks start =
    if start = 4173 then []
    else
      let count = min 16 (4173 - start) in
      let encoded_chunk =
        candle_case10173_registered_input_cval_list_slice
          start count encoded_jobs in
      let roots_chunk =
        candle_case10173_registered_input_cval_list_slice
          start count roots in
      let call =
        list_mk_comb
          (operator,[source_program;encoded_chunk;roots_chunk]) in
      {registered_chunk_start = start;
       registered_chunk_count = count;
       registered_chunk_encoded_jobs = encoded_chunk;
       registered_chunk_roots = roots_chunk;
       registered_chunk_call = call} ::
      chunks (start + count) in
  let chunk_list = chunks 0 in
  let groups = candle_case10173_registered_groups 16 chunk_list in
  let group_calls =
    map
      (fun group ->
        candle_case10173_registered_pair_tree
          (candle_case10173_registered_pad 16 `Cexp_num 1`
            (map (fun chunk -> chunk.registered_chunk_call) group)))
      groups in
  let group_results =
    map
      (fun group ->
        candle_case10173_registered_pair_tree
          (candle_case10173_registered_pad 16 `Cexp_num 1`
            (map (fun _ -> `Cexp_num 1`) group)))
      groups in
  if length chunk_list <> 261 || length groups <> 17 then
    failwith "case10173 registered ledger input: chunk/group count drift";
  {registered_ledger_chunks = chunk_list;
   registered_ledger_full_encoded_jobs = encoded_jobs;
   registered_ledger_call =
     candle_case10173_registered_pair_tree
       (candle_case10173_registered_pad 32 `Cexp_num 1` group_calls);
   registered_ledger_expected_result =
     candle_case10173_registered_pair_tree
       (candle_case10173_registered_pad 32 `Cexp_num 1` group_results)};;

let candle_case10173_registered_is_checked_call term =
  let operator,_ = strip_comb term in
  is_const operator &&
  fst (dest_const operator) =
    "candle_cv_case10173_hist_checked_raw_jobs_check";;

let candle_case10173_historical_registered_checked_theorems
    ledger theorem =
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) ledger.registered_ledger_call) ||
     not
       (aconv
         (rand (concl theorem)) ledger.registered_ledger_expected_result)
  then failwith "case10173 registered ledger input: aggregate mismatch";
  let leaves =
    candle_case10173_hist_registered_pair_result_leaves theorem in
  let checked,padding =
    List.partition
      (fun leaf ->
        candle_case10173_registered_is_checked_call (lhand (concl leaf)))
      leaves in
  if length checked <> 261 || length padding <> 26 ||
     not
       (List.for_all
         (fun leaf ->
           hyp leaf = [] &&
           aconv (lhand (concl leaf)) `Cexp_num 1` &&
           aconv (rand (concl leaf)) `Cexp_num 1`)
         padding) ||
     not
       (candle_case10173_registered_for_all2
         (fun chunk leaf ->
           hyp leaf = [] &&
           aconv (lhand (concl leaf)) chunk.registered_chunk_call &&
           aconv (rand (concl leaf)) `Cexp_num 1`)
         ledger.registered_ledger_chunks checked)
  then failwith "case10173 registered ledger input: leaf mismatch";
  checked;;

let candle_case10173_historical_registered_well_formed_theorem chunk =
  let call =
    mk_comb
      (`candle_cv_case10173_hist_jobs_well_formed`,
       chunk.registered_chunk_encoded_jobs) in
  let theorem =
    Kernel.compute
      (COMPUTE_INIT_THMS,
       candle_cv_case10173_hist_jobs_well_formed_compute_eqs)
      call in
  if hyp theorem <> [] ||
     not (aconv (lhand (concl theorem)) call) ||
     not (aconv (rand (concl theorem)) `Cexp_num 1`)
  then failwith "case10173 registered ledger input: structural guard failed";
  theorem;;

let candle_case10173_historical_registered_well_formed_theorems ledger =
  map candle_case10173_historical_registered_well_formed_theorem
    ledger.registered_ledger_chunks;;

let candle_case10173_historical_registered_acceptance
    ledger well_formed checked =
  let rec make chunks well_formed checked =
    match chunks,well_formed,checked with
    | [],[],[] -> []
    | chunk :: remaining_chunks,
      structural :: remaining_structural,
      numerical :: remaining_numerical ->
        candle_case10173_hist_registered_acceptance_of_theorems
          chunk.registered_chunk_encoded_jobs
          chunk.registered_chunk_roots structural numerical ::
        make remaining_chunks remaining_structural remaining_numerical
    | _ ->
        failwith "case10173 registered ledger input: theorem-count drift" in
  let result =
    candle_case10173_hist_registered_acceptance_collapse
      (make ledger.registered_ledger_chunks well_formed checked) in
  if result.registered_acceptance_chunk_count <> 261 ||
     not
       (aconv result.registered_acceptance_encoded_jobs
         ledger.registered_ledger_full_encoded_jobs)
  then failwith "case10173 registered ledger input: combined result drift";
  result;;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_LEDGER_INPUT_OK DEVELOPMENT_NON_RELEASE";;

end;;
