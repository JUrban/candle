(* ========================================================================== *)
(* Historical dihedral second-order Kernel.compute discriminator.            *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Exact native square-root  *)
(* intervals are sealed inputs.  The historical value, gradient, and full    *)
(* symmetric Hessian are recomputed inside Kernel.compute on genuine boxes.  *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_historical_dihedral_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_historical_dihedral_second_prefix128 = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_fixed_scale_historical_dihedral_compute;;
open Candle_cv_analytic_expr_jet_prove;;

let candle_case10173_hist_second_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_historical_dihedral_second_prefix128.tsv";;

let candle_case10173_hist_second_fields line =
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

let rec candle_case10173_hist_second_nth index items =
  match items with
  | [] -> failwith "case10173 historical second: fixture index"
  | head :: tail ->
      if index = 0 then head
      else candle_case10173_hist_second_nth (index - 1) tail;;

let candle_case10173_hist_second_signed text =
  let length = String.length text in
  if length = 0 then failwith "case10173 historical second: empty integer";
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

let candle_case10173_hist_second_interval fields offset =
  list_mk_comb
    (`Cexp_pair`,
     [candle_case10173_hist_second_signed
        (candle_case10173_hist_second_nth offset fields);
      candle_case10173_hist_second_signed
        (candle_case10173_hist_second_nth (offset + 1) fields)]);;

let candle_case10173_hist_second_list items =
  itlist (fun item result -> list_mk_comb (`Cexp_pair`,[item;result]))
    items `Cexp_num 0`;;

let candle_case10173_hist_second_upper_index row column =
  let lower = min row column in
  let upper = max row column in
  lower * (13 - lower) / 2 + upper - lower;;

let candle_case10173_hist_second_record expected_index line =
  let fields = candle_case10173_hist_second_fields line in
  if length fields <> 73 || int_of_string (hd fields) <> expected_index then
    failwith "case10173 historical second: fixture shape/index drift";
  let environment = candle_case10173_hist_second_list
    (map (fun coordinate ->
       candle_case10173_hist_second_interval fields (1 + 2 * coordinate))
      [0;1;2;3;4;5]) in
  let root_delta = candle_case10173_hist_second_interval fields 13 in
  let root_four_x0 = candle_case10173_hist_second_interval fields 15 in
  let expected_value = candle_case10173_hist_second_interval fields 17 in
  let expected_gradient = candle_case10173_hist_second_list
    (map (fun coordinate ->
       candle_case10173_hist_second_interval fields (19 + 2 * coordinate))
      [0;1;2;3;4;5]) in
  let expected_hessian = candle_case10173_hist_second_list
    (map (fun row -> candle_case10173_hist_second_list
       (map (fun column ->
          candle_case10173_hist_second_interval fields
            (31 + 2 * candle_case10173_hist_second_upper_index row column))
         [0;1;2;3;4;5]))
      [0;1;2;3;4;5]) in
  let input = candle_case10173_hist_second_list
    [environment;root_delta;root_four_x0] in
  let expected = list_mk_comb
    (`Cexp_pair`,
     [expected_value;
      list_mk_comb (`Cexp_pair`,[expected_gradient;expected_hessian])]) in
  input,expected;;

let candle_case10173_hist_second_prefix128 =
  print_endline "CANDLE_HIST_SECOND_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_hist_second_fixture_path in
  let rec read index inputs expected =
    try
      let input,result = candle_case10173_hist_second_record index
        (Stdlib.input_line channel) in
      read (index + 1) (input :: inputs) (result :: expected)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 128 then
        failwith "case10173 historical second: fixture record-count drift";
      candle_case10173_hist_second_list (rev inputs),
      candle_case10173_hist_second_list (rev expected) in
  let result = read 0 [] [] in
  print_endline "CANDLE_HIST_SECOND_FIXTURE_LOAD_END records=128";
  result;;

let candle_case10173_hist_second_inputs,
    candle_case10173_hist_second_expected =
  candle_case10173_hist_second_prefix128;;

let candle_cv_fs_hist_second_record_def = new_definition
 `candle_cv_fs_hist_second_record record =
    candle_cv_fs_hist_second_order
      (candle_cv_fs_interval_lookup (Cexp_num 0) record)
      (candle_cv_fs_interval_lookup (Cexp_num 1) record)
      (candle_cv_fs_interval_lookup (Cexp_num 2) record)`;;

let candle_cv_fs_hist_second_records_def = define
 `(candle_cv_fs_hist_second_records (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_hist_second_records (Cexp_pair record records) =
     Cexp_pair (candle_cv_fs_hist_second_record record)
       (candle_cv_fs_hist_second_records records))`;;

let candle_cv_fs_hist_second_records_compute = prove
 (`!records.
     candle_cv_fs_hist_second_records records =
     Cexp_if (Cexp_ispair records)
       (Cexp_pair
         (candle_cv_fs_hist_second_record (Cexp_fst records))
         (candle_cv_fs_hist_second_records (Cexp_snd records)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `records:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_hist_second_records_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_case10173_hist_second_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fs_hist_first_compute_eqs
      (map SPEC_ALL
        [candle_cv_fs_hist_second_record_def;
         candle_cv_fs_hist_second_records_compute]));;

let _ =
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-historical-second-prefix128" ^
       " phase=" ^ event));
  let call = mk_comb
    (`candle_cv_fs_hist_second_records`,
     candle_case10173_hist_second_inputs) in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-begin";
  let theorem = candle_q_dim_analytic_jet_compute
    candle_case10173_hist_second_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event "kernel-compute-end";
  candle_q_dim_analytic_jet_profile_event "handoff-begin";
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) then
    failwith "case10173 historical second: open or malformed theorem";
  if not (aconv (rand (concl theorem))
        candle_case10173_hist_second_expected) then
    failwith "case10173 historical second: exact native stage mismatch";
  candle_q_dim_analytic_jet_profile_event "handoff-end";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 historical second: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_HISTORICAL_SECOND_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 exact_native_stage=128 assumptions=0 axiom_growth=0 roots_inside_compute=0 delta_inside_compute=1 u_inside_compute=1 inverse_inside_compute=1 atan_inside_compute=1 hessian_inside_compute=1";;

end;;
