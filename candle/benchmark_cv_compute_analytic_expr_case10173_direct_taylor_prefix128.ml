(* ========================================================================== *)
(* Direct-plan final-Taylor Kernel.compute lower bound on case 10173.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  Native preparation has    *)
(* already supplied each complete center tangent and box Hessian absolute     *)
(* bound.  This benchmark measures only encoded traversal, the final Taylor   *)
(* completion, theorem production, and result handoff.  It is deliberately    *)
(* not the direct reflected checker: the dihedral tangent and Hessian still   *)
(* have to move inside Kernel.compute before that milestone is reached.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_direct_taylor_prefix128 = struct

open Candle_cv_analytic_expr_fixed_scale_compute;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;

let candle_case10173_direct_stage_fixture_path =
  file_on_path (!load_path)
    "candle/fixtures/case10173_direct_stage_prefix128.tsv";;

let candle_case10173_direct_stage_cval_num value =
  mk_comb (`Cexp_num`,mk_numeral value);;

let candle_case10173_direct_stage_cval_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_case10173_direct_stage_cval_signed text =
  let length = String.length text in
  if length = 0 then failwith "case10173 direct stage: empty integer";
  if String.get text 0 = '-' then
    candle_case10173_direct_stage_cval_pair
      (candle_case10173_direct_stage_cval_num (Num.num_of_int 0))
      (candle_case10173_direct_stage_cval_num
        (Num.num_of_string (String.sub text 1 (length - 1))))
  else
    candle_case10173_direct_stage_cval_pair
      (candle_case10173_direct_stage_cval_num (Num.num_of_string text))
      (candle_case10173_direct_stage_cval_num (Num.num_of_int 0));;

let candle_case10173_direct_stage_cval_list items =
  itlist candle_case10173_direct_stage_cval_pair items `Cexp_num 0`;;

let rec candle_case10173_direct_stage_take count items =
  if count = 0 then [] else
  match items with
  | [] -> failwith "case10173 direct stage: short fixture record"
  | head :: tail ->
      head :: candle_case10173_direct_stage_take (count - 1) tail;;

let rec candle_case10173_direct_stage_drop count items =
  if count = 0 then items else
  match items with
  | [] -> failwith "case10173 direct stage: short fixture record"
  | _ :: tail -> candle_case10173_direct_stage_drop (count - 1) tail;;

let rec candle_case10173_direct_stage_nth index items =
  match items with
  | [] -> failwith "case10173 direct stage: fixture index"
  | head :: tail ->
      if index = 0 then head
      else candle_case10173_direct_stage_nth (index - 1) tail;;

let candle_case10173_direct_stage_abs_interval text =
  let value = candle_case10173_direct_stage_cval_signed text in
  let negative = candle_case10173_direct_stage_cval_signed ("-" ^ text) in
  candle_case10173_direct_stage_cval_pair
    negative value;;

let candle_case10173_direct_stage_fields line =
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

let candle_case10173_direct_stage_record expected_index line =
  let fields = candle_case10173_direct_stage_fields line in
  if expected_index = 0 then
    print_endline
      ("CANDLE_DIRECT_STAGE_FIXTURE_FIELDS count=" ^
       string_of_int (length fields));
  if length fields <> 36 || int_of_string (hd fields) <> expected_index then
    failwith "case10173 direct stage: fixture shape/index drift";
  let center_upper = candle_case10173_direct_stage_cval_signed
    (candle_case10173_direct_stage_nth 1 fields) in
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_CENTER_OK";
  let radii = map candle_case10173_direct_stage_cval_signed
    (candle_case10173_direct_stage_take 6
      (candle_case10173_direct_stage_drop 2 fields)) in
  let gradient_abs = candle_case10173_direct_stage_take 6
    (candle_case10173_direct_stage_drop 8 fields) in
  let hessian_abs = candle_case10173_direct_stage_take 21
    (candle_case10173_direct_stage_drop 14 fields) in
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_SCALARS_OK";
  let hessian_index row column =
    let first,second = if row <= column then row,column else column,row in
    first * 6 - first * (first + 1) / 2 + second in
  let hessian =
    map
      (fun row ->
        candle_case10173_direct_stage_cval_list
          (map
            (fun column ->
              candle_case10173_direct_stage_abs_interval
                (candle_case10173_direct_stage_nth
                  (hessian_index row column) hessian_abs))
            [0;1;2;3;4;5]))
      [0;1;2;3;4;5] in
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_HESSIAN_OK";
  let center = candle_case10173_direct_stage_cval_pair
    center_upper center_upper in
  let gradient = map candle_case10173_direct_stage_abs_interval gradient_abs in
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_GRADIENT_OK";
  let expected = candle_case10173_direct_stage_nth 35 fields in
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_EXPECTED_OK";
  if expected_index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_TERMS_OK";
  candle_case10173_direct_stage_cval_list
    [center;
     candle_case10173_direct_stage_cval_list radii;
     candle_case10173_direct_stage_cval_list gradient;
     candle_case10173_direct_stage_cval_list hessian],expected;;

let candle_case10173_direct_stage_prefix128 =
  print_endline "CANDLE_DIRECT_STAGE_FIXTURE_LOAD_BEGIN";
  let channel = Stdlib.open_in candle_case10173_direct_stage_fixture_path in
  print_endline "CANDLE_DIRECT_STAGE_FIXTURE_OPEN_OK";
  let rec read index records expected =
    try
      let line = Stdlib.input_line channel in
      if index = 0 then print_endline "CANDLE_DIRECT_STAGE_FIXTURE_LINE_OK";
      let record,bound = candle_case10173_direct_stage_record index line in
      read (index + 1) (record :: records) (bound :: expected)
    with End_of_file ->
      Stdlib.close_in channel;
      if index <> 128 then
        failwith "case10173 direct stage: fixture record-count drift";
      candle_case10173_direct_stage_cval_list (rev records),rev expected in
  let result = read 0 [] [] in
  print_endline "CANDLE_DIRECT_STAGE_FIXTURE_LOAD_END records=128";
  result;;

let candle_case10173_direct_stage_records,
    candle_case10173_direct_stage_expected =
  candle_case10173_direct_stage_prefix128;;

let candle_cv_direct_stage_field_def = new_definition
 `candle_cv_direct_stage_field position record =
    candle_cv_fs_interval_lookup position record`;;

let candle_cv_direct_stage_complete_def = new_definition
 `candle_cv_direct_stage_complete record =
    let center = candle_cv_direct_stage_field (Cexp_num 0) record in
    let radii = candle_cv_direct_stage_field (Cexp_num 1) record in
    let gradient = candle_cv_direct_stage_field (Cexp_num 2) record in
    let hessian = candle_cv_direct_stage_field (Cexp_num 3) record in
    let result = candle_cv_fs_result_complete_rounded radii (Cexp_num 1)
      (candle_cv_fs_first_make center gradient) hessian in
    Cexp_snd (candle_cv_fs_result_value_bound result)`;;

let candle_cv_direct_stage_minimal_def = new_definition
 `candle_cv_direct_stage_minimal record =
    let center = candle_cv_direct_stage_field (Cexp_num 0) record in
    let radii = candle_cv_direct_stage_field (Cexp_num 1) record in
    let gradient = candle_cv_direct_stage_field (Cexp_num 2) record in
    let hessian = candle_cv_direct_stage_field (Cexp_num 3) record in
    let linear = candle_cv_fs_dot_abs_upper radii gradient in
    let quadratic =
      candle_cv_fs_weighted_rows_abs_upper radii radii hessian in
    let error = candle_cv_fs_raw_add
      (candle_cv_fs_raw_scale
        (Cexp_mul (Cexp_num 2) candle_cv_fs_scale) linear)
      quadratic in
    let raw_upper = candle_cv_fs_raw_add
      (candle_cv_fs_raw_scale candle_cv_fs_two_scale_squared
        (Cexp_snd center)) error in
    candle_cv_fs_ceil_div raw_upper candle_cv_fs_two_scale_squared`;;

let candle_cv_direct_stage_map_def = define
 `(candle_cv_direct_stage_map use_minimal (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_direct_stage_map use_minimal (Cexp_pair record records) =
     Cexp_pair
       (Cexp_if use_minimal
         (candle_cv_direct_stage_minimal record)
         (candle_cv_direct_stage_complete record))
       (candle_cv_direct_stage_map use_minimal records))`;;

let candle_cv_direct_stage_map_compute = prove
 (`!use_minimal records.
     candle_cv_direct_stage_map use_minimal records =
     Cexp_if (Cexp_ispair records)
       (Cexp_pair
         (Cexp_if use_minimal
           (candle_cv_direct_stage_minimal (Cexp_fst records))
           (candle_cv_direct_stage_complete (Cexp_fst records)))
         (candle_cv_direct_stage_map use_minimal (Cexp_snd records)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `records:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_direct_stage_map_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_case10173_direct_stage_compute_eqs =
  map (REWRITE_RULE [LET_END_DEF])
    (union candle_cv_fs_compute_eqs
      (map SPEC_ALL
        [candle_cv_direct_stage_field_def;
         candle_cv_direct_stage_complete_def;
         candle_cv_direct_stage_minimal_def;
         candle_cv_direct_stage_map_compute]));;

let candle_case10173_direct_stage_matches label term expected =
  let positive,negative =
    candle_q_dim_stable_program_dest_cval_pair label term in
  let dest_num term =
    let constructor,arguments = strip_comb term in
    if not (aconv constructor `Cexp_num`) then
      failwith (label ^ ": expected fixed numeral");
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith (label ^ ": malformed fixed numeral") in
  let positive_num = dest_num positive
  and negative_num = dest_num negative in
  let zero = Num.num_of_int 0 in
  let length = String.length expected in
  if length = 0 then failwith (label ^ ": empty expected integer");
  if String.get expected 0 = '-' then
    Num.eq_num positive_num zero &&
    Num.string_of_num negative_num = String.sub expected 1 (length - 1)
  else
    Num.eq_num negative_num zero && Num.string_of_num positive_num = expected;;

let candle_case10173_direct_stage_signed_string label term =
  let positive,negative =
    candle_q_dim_stable_program_dest_cval_pair label term in
  let dest_num term =
    let constructor,arguments = strip_comb term in
    if not (aconv constructor `Cexp_num`) then
      failwith (label ^ ": expected fixed numeral");
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith (label ^ ": malformed fixed numeral") in
  let positive_num = dest_num positive
  and negative_num = dest_num negative in
  if Num.eq_num positive_num (Num.num_of_int 0) then
    "-" ^ Num.string_of_num negative_num
  else Num.string_of_num positive_num;;

let rec candle_case10173_direct_stage_results label term expected =
  if aconv term `Cexp_num 0` then
    match expected with
    | [] -> 0
    | _ -> failwith (label ^ ": short computed result")
  else
  let actual,remaining =
    candle_q_dim_stable_program_dest_cval_pair label term in
  match expected with
  | [] -> failwith (label ^ ": extra computed result")
  | bound :: bounds ->
      if not (candle_case10173_direct_stage_matches label actual bound)
      then failwith
        (label ^ ": native bound mismatch actual=" ^
         candle_case10173_direct_stage_signed_string label actual ^
         " expected=" ^ bound);
      1 + candle_case10173_direct_stage_results
        label remaining bounds;;

let candle_case10173_direct_stage_run label use_minimal =
  candle_q_dim_analytic_jet_profile_event (label ^ "-compute-begin");
  let call = list_mk_comb
    (`candle_cv_direct_stage_map`,
     [use_minimal;candle_case10173_direct_stage_records]) in
  let theorem = candle_q_dim_analytic_jet_compute
    candle_case10173_direct_stage_compute_eqs call in
  candle_q_dim_analytic_jet_profile_event (label ^ "-compute-end");
  if hyp theorem <> [] || not (aconv (lhand (concl theorem)) call) then
    failwith (label ^ ": open or malformed theorem");
  candle_q_dim_analytic_jet_profile_event (label ^ "-handoff-begin");
  let count = candle_case10173_direct_stage_results
    ("case10173 " ^ label) (rand (concl theorem))
    candle_case10173_direct_stage_expected in
  candle_q_dim_analytic_jet_profile_event (label ^ "-handoff-end");
  if count <> 128 then failwith (label ^ ": result-count drift");
  theorem;;

let _ =
  let axioms_before = axioms () in
  candle_q_dim_analytic_jet_profile :=
    (fun event -> print_endline
      ("CANDLE_CERT_PROFILE lane=case10173-direct-taylor-prefix128 phase=" ^
       event));
  let complete = candle_case10173_direct_stage_run
    "complete" `Cexp_num 0` in
  let minimal = candle_case10173_direct_stage_run
    "minimal" `Cexp_num 1` in
  if not (aconv (rand (concl complete)) (rand (concl minimal))) then
    failwith "case10173 direct Taylor: lane mismatch";
  let axioms_after = axioms () in
  if length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 direct Taylor: axiom-set drift";
  print_endline
    "CANDLE_CV_CASE10173_DIRECT_TAYLOR_PREFIX128_OK DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE cells=128 exact_native_bounds=128 assumptions=0 axiom_growth=0 dihedral_inside_compute=0";;

end;;
