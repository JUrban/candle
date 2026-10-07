(* ========================================================================== *)
(* Compact whole-expression benchmark on 128 genuine case-10173 jobs.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The compact plan is      *)
(* extracted only after validating the complete expected source skeleton.    *)
(* Four historical auxiliary root intervals remain supplied benchmark data.  *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_case10173_compact_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_compact_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_case10173_compact_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_case10173_compact_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_prefix128.tsv";;

let candle_case10173_compact_fields line =
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

let rec candle_case10173_compact_nth index items =
  match items with
  | [] -> failwith "case10173 compact: index"
  | head :: tail ->
      if index = 0 then head
      else candle_case10173_compact_nth (index - 1) tail;;

let candle_case10173_compact_signed text =
  let length = String.length text in
  if length = 0 then failwith "case10173 compact: empty integer";
  if String.get text 0 = '-' then
    list_mk_comb
      (`Cexp_pair`,
       [`Cexp_num 0`;
        mk_comb (`Cexp_num`,mk_numeral
          (Num.num_of_string (String.sub text 1 (length - 1))))])
  else
    list_mk_comb
      (`Cexp_pair`,
       [mk_comb (`Cexp_num`,mk_numeral (Num.num_of_string text));
        `Cexp_num 0`]);;

let candle_case10173_compact_interval fields offset =
  list_mk_comb
    (`Cexp_pair`,
     [candle_case10173_compact_signed
        (candle_case10173_compact_nth offset fields);
      candle_case10173_compact_signed
        (candle_case10173_compact_nth (offset + 1) fields)]);;

let candle_case10173_compact_list items =
  itlist (fun item result -> list_mk_comb (`Cexp_pair`,[item;result]))
    items `Cexp_num 0`;;

let candle_case10173_compact_root_record expected_index line =
  let fields = candle_case10173_compact_fields line in
  if length fields <> 9 || int_of_string (hd fields) <> expected_index then
    failwith "case10173 compact: fixture shape/index drift";
  candle_case10173_compact_list
    (map (fun root ->
       candle_case10173_compact_interval fields (1 + 2 * root))
      [0;1;2;3]);;

let candle_case10173_compact_roots =
  print_endline "CANDLE_COMPACT_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_compact_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_compact_root_record index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 128 then
        failwith "case10173 compact: fixture record-count drift";
      candle_case10173_compact_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_COMPACT_FIXTURE_LOAD_END records=128";
  result;;

let rec candle_case10173_compact_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail = candle_q_dim_stable_program_dest_cval_pair
    "case10173 compact prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_compact_take (count - 1) tail);;

let rec candle_case10173_compact_program_items encoded =
  if aconv encoded `Cexp_num 0` then [] else
  let head,tail = candle_q_dim_stable_program_dest_cval_pair
    "case10173 compact program" encoded in
  head :: candle_case10173_compact_program_items tail;;

let candle_case10173_compact_num expected term =
  aconv term (mk_comb (`Cexp_num`,mk_small_numeral expected));;

let candle_case10173_compact_pair term =
  candle_q_dim_stable_program_dest_cval_pair
    "case10173 compact paired instruction" term;;

let candle_case10173_compact_pair_tag expected term =
  let tag,_ = candle_case10173_compact_pair term in
  candle_case10173_compact_num expected tag;;

let candle_case10173_compact_poly_payload instruction =
  let tag,payload = candle_case10173_compact_pair instruction in
  if not (candle_case10173_compact_num 0 tag) then
    failwith "case10173 compact: expected polynomial instruction";
  payload;;

let candle_case10173_compact_singleton_poly inner_tag instruction =
  try
    let payload = candle_case10173_compact_poly_payload instruction in
    match candle_case10173_compact_program_items payload with
    | [inner] -> candle_case10173_compact_pair_tag inner_tag inner
    | _ -> false
  with Failure _ -> false;;

let candle_case10173_compact_poly_length expected instruction =
  try
    length
      (candle_case10173_compact_program_items
        (candle_case10173_compact_poly_payload instruction)) = expected
  with Failure _ -> false;;

let candle_case10173_compact_validate_source instructions =
  let constants = [0;5;10;15;20;25;30] and
      inputs = [1;6;11;16;21;26] and
      square_roots = [2;7;12;17;22;27] and
      coefficients = [3;8;13;18;23;28] and
      multiplies = [4;9;14;19;24;29] in
  length instructions = 54 &&
  List.for_all
    (fun index -> candle_case10173_compact_pair_tag 0
      (candle_case10173_compact_nth index instructions)) constants &&
  List.for_all
    (fun index -> candle_case10173_compact_pair_tag 0
      (candle_case10173_compact_nth index instructions)) inputs &&
  List.for_all
    (fun index -> candle_case10173_compact_pair_tag 1
      (candle_case10173_compact_nth index instructions)) square_roots &&
  List.for_all
    (fun index -> candle_case10173_compact_pair_tag 0
      (candle_case10173_compact_nth index instructions)) coefficients &&
  List.for_all
    (fun index -> candle_case10173_compact_num 4
      (candle_case10173_compact_nth index instructions)) multiplies &&
  candle_case10173_compact_num 8
    (candle_case10173_compact_nth 31 instructions) &&
  candle_case10173_compact_poly_length 39
    (candle_case10173_compact_nth 32 instructions) &&
  candle_case10173_compact_poly_length 85
    (candle_case10173_compact_nth 33 instructions) &&
  candle_case10173_compact_pair_tag 1
    (candle_case10173_compact_nth 34 instructions) &&
  candle_case10173_compact_num 6
    (candle_case10173_compact_nth 35 instructions) &&
  candle_case10173_compact_num 4
    (candle_case10173_compact_nth 36 instructions) &&
  candle_case10173_compact_num 7
    (candle_case10173_compact_nth 37 instructions) &&
  candle_case10173_compact_num 3
    (candle_case10173_compact_nth 38 instructions) &&
  candle_case10173_compact_pair_tag 0
    (candle_case10173_compact_nth 39 instructions) &&
  candle_case10173_compact_num 4
    (candle_case10173_compact_nth 40 instructions) &&
  List.for_all
    (fun index -> candle_case10173_compact_num 3
      (candle_case10173_compact_nth index instructions))
    [41;42;43;44;45;46;47;48;49;50;51;52;53];;

let candle_case10173_compact_plan instructions =
  let payloads indices =
    candle_case10173_compact_list
      (map (fun index -> candle_case10173_compact_poly_payload
        (candle_case10173_compact_nth index instructions)) indices) in
  candle_case10173_compact_list
    [payloads [0;5;10;15;20;25;30];
     payloads [1;6;11;16;21;26];
     payloads [3;8;13;18;23;28];
     candle_case10173_compact_poly_payload
       (candle_case10173_compact_nth 39 instructions)];;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-compact-prefix128 phase=" ^
       event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  candle_q_dim_analytic_jet_profile_event "plan-preparation-begin";
  let instructions = candle_case10173_compact_program_items source_program in
  if not (candle_case10173_compact_validate_source instructions) then
    failwith "case10173 compact: complete source skeleton drift";
  let plan = candle_case10173_compact_plan instructions in
  let encoded_jobs = candle_case10173_compact_take 128
    captured.case10173_complete_encoded_jobs in
  candle_q_dim_analytic_jet_profile_event "plan-preparation-end";
  let call = list_mk_comb
    (`candle_cv_case10173_compact_raw_jobs_check`,
     [plan;encoded_jobs;candle_case10173_compact_roots]) in
  let run label =
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem = candle_q_dim_analytic_jet_compute
      candle_cv_case10173_compact_compute_eqs call in
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
    theorem in
  let first = run "candidate-1" in
  let second = run "candidate-2" in
  if hyp first <> [] || hyp second <> [] ||
     not (aconv (lhand (concl first)) call) ||
     not (aconv (lhand (concl second)) call) ||
     not (aconv (rand (concl first)) `Cexp_num 1`) ||
     not (aconv (rand (concl second)) `Cexp_num 1`) ||
     length (axioms ()) <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) (axioms ()))
  then failwith "case10173 compact: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_COMPACT_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 candidates=2 result=1 source_instructions=54 source_skeleton_validated=1 plan_items=4 coordinate_terms=6 additive_constants=7 final_completions_per_cell=1 supplied_aux_roots=4 assumptions=0 axiom_growth=0";;

end;;
