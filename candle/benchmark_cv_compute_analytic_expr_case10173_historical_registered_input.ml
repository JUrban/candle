(* ========================================================================== *)
(* Data-only input for the complete genuine case-10173 historical checker.   *)
(*                                                                            *)
(* Constructing this input must not execute either the generic numerical      *)
(* checker or the registered fast checker.  This keeps reusable certificate   *)
(* preparation separate from the recurring trusted verdict.                   *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_checked_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_registered_input = struct

open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_outer_variable_raw_prove;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_checked_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_variable_raw_plan;;

type candle_case10173_historical_registered_input = {
  registered_input_source_program : term;
  registered_input_encoded_jobs : term;
  registered_input_roots : term;
  registered_input_checked_call : term;
};;

let candle_case10173_registered_input_fields line =
  let limit = String.length line in
  let space character =
    character = ' ' || character = '\t' ||
    character = '\r' || character = '\n' in
  let rec skip position =
    if position < limit && space (String.get line position) then
      skip (position + 1)
    else position in
  let rec finish position =
    if position < limit && not (space (String.get line position)) then
      finish (position + 1)
    else position in
  let rec fields position result =
    let first = skip position in
    if first >= limit then rev result else
    let last = finish first in
    fields last (String.sub line first (last - first) :: result) in
  fields 0 [];;

let rec candle_case10173_registered_input_nth index items =
  match items with
  | [] -> failwith "case10173 registered input: fixture index"
  | head :: tail ->
      if index = 0 then head
      else candle_case10173_registered_input_nth (index - 1) tail;;

let candle_case10173_registered_input_signed text =
  let count = String.length text in
  if count = 0 then failwith "case10173 registered input: empty integer";
  if String.get text 0 = '-' then
    list_mk_comb
      (`Cexp_pair`,
       [`Cexp_num 0`;
        mk_comb (`Cexp_num`,mk_numeral
          (Num.num_of_string (String.sub text 1 (count - 1))))])
  else
    list_mk_comb
      (`Cexp_pair`,
       [mk_comb (`Cexp_num`,mk_numeral (Num.num_of_string text));
        `Cexp_num 0`]);;

let candle_case10173_registered_input_interval fields offset =
  list_mk_comb
    (`Cexp_pair`,
     [candle_case10173_registered_input_signed
        (candle_case10173_registered_input_nth offset fields);
      candle_case10173_registered_input_signed
        (candle_case10173_registered_input_nth (offset + 1) fields)]);;

let candle_case10173_registered_input_list items =
  itlist (fun item result -> list_mk_comb (`Cexp_pair`,[item;result]))
    items `Cexp_num 0`;;

let candle_case10173_registered_input_root expected_index line =
  let fields = candle_case10173_registered_input_fields line in
  if length fields <> 9 || int_of_string (hd fields) <> expected_index then
    failwith "case10173 registered input: fixture shape/index drift";
  candle_case10173_registered_input_list
    (map
      (fun root ->
        candle_case10173_registered_input_interval fields (1 + 2 * root))
      [0;1;2;3]);;

let candle_case10173_registered_input_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_full4173.tsv";;

let candle_case10173_registered_input_roots () =
  print_endline "CANDLE_REGISTERED_INPUT_FIXTURE_LOAD_BEGIN";
  let channel =
    Stdlib.open_in candle_case10173_registered_input_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_registered_input_root index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 4173 then
        failwith "case10173 registered input: fixture record-count drift";
      candle_case10173_registered_input_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_REGISTERED_INPUT_FIXTURE_LOAD_END records=4173";
  result;;

let candle_case10173_registered_input_cval_list_view encoded =
  let operator,arguments = strip_comb encoded in
  let name,_ = dest_const operator in
  match name,arguments with
  | "Cexp_num",[zero] when dest_numeral zero =/ Num.num_of_int 0 -> None
  | "Cexp_pair",[head;tail] -> Some (head,tail)
  | _ -> failwith "case10173 registered input: malformed cval list";;

let rec candle_case10173_registered_input_cval_list_length encoded =
  match candle_case10173_registered_input_cval_list_view encoded with
  | None -> 0
  | Some (_,tail) ->
      1 + candle_case10173_registered_input_cval_list_length tail;;

let rec candle_case10173_registered_input_cval_list_drop count encoded =
  if count = 0 then encoded
  else
    match candle_case10173_registered_input_cval_list_view encoded with
    | Some (_,tail) ->
        candle_case10173_registered_input_cval_list_drop (count - 1) tail
    | None -> failwith "case10173 registered input: drop exceeds list";;

let rec candle_case10173_registered_input_cval_list_take count encoded =
  if count = 0 then `Cexp_num 0`
  else
    match candle_case10173_registered_input_cval_list_view encoded with
    | Some (head,tail) ->
        list_mk_comb
          (`Cexp_pair`,
           [head;
            candle_case10173_registered_input_cval_list_take
              (count - 1) tail])
    | None -> failwith "case10173 registered input: take exceeds list";;

let candle_case10173_registered_input_cval_list_slice start count encoded =
  candle_case10173_registered_input_cval_list_take count
    (candle_case10173_registered_input_cval_list_drop start encoded);;

let candle_case10173_historical_registered_input_state :
    candle_case10173_historical_registered_input option ref = ref None;;

let candle_case10173_historical_registered_input () =
  match !candle_case10173_historical_registered_input_state with
  | Some input -> input
  | None ->
      print_endline "CANDLE_REGISTERED_INPUT_CONSTRUCTION_BEGIN";
      let plan = candle_case10173_variable_raw_plan () in
      let source_program =
        plan.case10173_variable_raw_plan_prepared.program_representation_term in
      let encoded_jobs =
        candle_q_dim_taylor_model_fixed_outer_variable_raw_encode_cells_six
          plan.case10173_variable_raw_plan_cells in
      let roots = candle_case10173_registered_input_roots () in
      if candle_case10173_registered_input_cval_list_length encoded_jobs <> 4173 ||
         candle_case10173_registered_input_cval_list_length roots <> 4173
      then failwith "case10173 registered input: aligned-list drift";
      let checked_call =
        list_mk_comb
          (`candle_cv_case10173_hist_checked_raw_jobs_check`,
           [source_program;encoded_jobs;roots]) in
      let input = {
        registered_input_source_program = source_program;
        registered_input_encoded_jobs = encoded_jobs;
        registered_input_roots = roots;
        registered_input_checked_call = checked_call;
      } in
      candle_case10173_historical_registered_input_state := Some input;
      print_endline
        "CANDLE_REGISTERED_INPUT_CONSTRUCTION_END cells=4173 numerical_compute=0";
      input;;

print_endline
  "CANDLE_CV_CASE10173_HISTORICAL_REGISTERED_INPUT_OK DEVELOPMENT_NON_RELEASE";;

end;;
