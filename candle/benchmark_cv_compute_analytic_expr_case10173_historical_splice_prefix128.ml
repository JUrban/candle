(* ========================================================================== *)
(* Whole-program historical-dihedral splice on 128 genuine case-10173 jobs.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  The authenticated source  *)
(* program and existing seven sqrt certificates are checked unchanged.  The  *)
(* exact source segment at outer instructions 31--38 is replaced by the      *)
(* historical fixed-scale operation using four sealed auxiliary roots.       *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;
needs "candle/cv_compute_analytic_expr_case10173_historical_dihedral_program_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_splice_prefix128 = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Candle_cv_analytic_expr_case10173_historical_dihedral_program_compute;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

let candle_case10173_hist_splice_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_roots_prefix128.tsv";;

let candle_case10173_hist_splice_fields line =
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

let rec candle_case10173_hist_splice_nth index items =
  match items with
  | [] -> failwith "case10173 historical splice: fixture index"
  | head :: tail ->
      if index = 0 then head
      else candle_case10173_hist_splice_nth (index - 1) tail;;

let candle_case10173_hist_splice_signed text =
  let length = String.length text in
  if length = 0 then failwith "case10173 historical splice: empty integer";
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

let candle_case10173_hist_splice_interval fields offset =
  list_mk_comb
    (`Cexp_pair`,
     [candle_case10173_hist_splice_signed
        (candle_case10173_hist_splice_nth offset fields);
      candle_case10173_hist_splice_signed
        (candle_case10173_hist_splice_nth (offset + 1) fields)]);;

let candle_case10173_hist_splice_list items =
  itlist (fun item result -> list_mk_comb (`Cexp_pair`,[item;result]))
    items `Cexp_num 0`;;

let candle_case10173_hist_splice_record expected_index line =
  let fields = candle_case10173_hist_splice_fields line in
  if length fields <> 9 || int_of_string (hd fields) <> expected_index then
    failwith "case10173 historical splice: fixture shape/index drift";
  candle_case10173_hist_splice_list
    (map (fun root ->
       candle_case10173_hist_splice_interval fields (1 + 2 * root))
      [0;1;2;3]);;

let candle_case10173_hist_splice_roots =
  print_endline "CANDLE_HIST_SPLICE_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_hist_splice_fixture_path in
  let rec read index roots =
    try
      let root = candle_case10173_hist_splice_record index
        (Stdlib.input_line channel) in
      read (index + 1) (root :: roots)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 128 then
        failwith "case10173 historical splice: fixture record-count drift";
      candle_case10173_hist_splice_list (rev roots) in
  let result = read 0 [] in
  print_endline "CANDLE_HIST_SPLICE_FIXTURE_LOAD_END records=128";
  result;;

let rec candle_case10173_hist_splice_take count encoded =
  if count = 0 then `Cexp_num 0` else
  let head,tail = candle_q_dim_stable_program_dest_cval_pair
    "case10173 historical splice prefix" encoded in
  candle_q_dim_stable_program_cval_pair head
    (candle_case10173_hist_splice_take (count - 1) tail);;

let rec candle_case10173_hist_splice_program_items encoded =
  if aconv encoded `Cexp_num 0` then [] else
  let head,tail = candle_q_dim_stable_program_dest_cval_pair
    "case10173 historical splice program" encoded in
  head :: candle_case10173_hist_splice_program_items tail;;

let candle_case10173_hist_splice_num expected term =
  aconv term (mk_comb (`Cexp_num`,mk_small_numeral expected));;

let candle_case10173_hist_splice_poly_length expected term =
  let tag,payload = candle_q_dim_stable_program_dest_cval_pair
    "case10173 historical splice polynomial" term in
  candle_case10173_hist_splice_num 0 tag &&
  length (candle_case10173_hist_splice_program_items payload) = expected;;

let candle_case10173_hist_splice_pair_tag expected term =
  let tag,_ = candle_q_dim_stable_program_dest_cval_pair
    "case10173 historical splice tagged instruction" term in
  candle_case10173_hist_splice_num expected tag;;

let candle_case10173_hist_splice_validate_source source_program =
  let instructions =
    candle_case10173_hist_splice_program_items source_program in
  length instructions = 54 &&
  candle_case10173_hist_splice_num 8
    (candle_case10173_hist_splice_nth 31 instructions) &&
  candle_case10173_hist_splice_poly_length 39
    (candle_case10173_hist_splice_nth 32 instructions) &&
  candle_case10173_hist_splice_poly_length 85
    (candle_case10173_hist_splice_nth 33 instructions) &&
  candle_case10173_hist_splice_pair_tag 1
    (candle_case10173_hist_splice_nth 34 instructions) &&
  candle_case10173_hist_splice_num 6
    (candle_case10173_hist_splice_nth 35 instructions) &&
  candle_case10173_hist_splice_num 4
    (candle_case10173_hist_splice_nth 36 instructions) &&
  candle_case10173_hist_splice_num 7
    (candle_case10173_hist_splice_nth 37 instructions) &&
  candle_case10173_hist_splice_num 3
    (candle_case10173_hist_splice_nth 38 instructions);;

let _ =
  Candle_cv_analytic_expr_jet_prove.candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-historical-splice-prefix128" ^
       " phase=" ^ event));
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  if not (candle_case10173_hist_splice_validate_source source_program) then
    failwith "case10173 historical splice: source segment drift";
  let encoded_jobs = candle_case10173_hist_splice_take 128
    captured.case10173_complete_encoded_jobs in
  let call = list_mk_comb
    (`candle_cv_case10173_hist_raw_jobs_check`,
     [source_program;encoded_jobs;candle_case10173_hist_splice_roots]) in
  let run label =
    candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
    let theorem = candle_q_dim_analytic_jet_compute
      candle_cv_case10173_hist_program_compute_eqs call in
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
  then failwith "case10173 historical splice: validation failed";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_SPLICE_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 candidate=2 result=1 source_instructions=54 replaced_first=31 replaced_last=38 sealed_aux_roots=4 assumptions=0 axiom_growth=0";;

end;;
