(* ========================================================================== *)
(* Whole-leaf coverage over 32 genuine action-296 precision-tree leaves.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Consecutive groups of four share source and  *)
(* point-plan preparation.  Each group returns only four acceptance flags.    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_adaptive_grouping_algebraic.ml";;

let candle_action296_grouped_32_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-grouped-32-algebraic" ^
     " scope=whole-leaves phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_grouped_32_domains,_ =
  candle_action296_leaf_grouping_take 32
    !candle_action296_leaf_grouping_leaves;;

let candle_action296_grouped_32_groups =
  candle_action296_leaf_grouping_partition 4
    candle_action296_grouped_32_domains;;

let rec candle_action296_grouped_32_prepare_group domains =
  try
    let lower,upper =
      candle_action296_leaf_grouping_envelope domains in
    [domains,
     candle_q_dim_analytic_jet_prepare_box_six
       candle_action296_plan_prepared.function_term lower upper]
  with Failure message ->
    if message <> "analytic box certificate: nonpositive square-root range" then
      failwith message;
    let group_length = length domains in
    if group_length <= 1 then
      failwith
        "action296 grouped 32: individual leaf has nonpositive square-root range";
    let left,right =
      candle_action296_leaf_grouping_take (group_length / 2) domains in
    candle_action296_grouped_32_prepare_group left @
    candle_action296_grouped_32_prepare_group right;;

let _ =
  candle_action296_grouped_32_marker "source-preparation" "begin";;
let candle_action296_grouped_32_prepared_ref :
    (thm list * candle_q_dim_analytic_jet_prepared_six) list option ref =
  ref None;;
let _ =
  candle_action296_grouped_32_prepared_ref :=
    Some
      (List.flatten
        (map candle_action296_grouped_32_prepare_group
          candle_action296_grouped_32_groups));;
let _ =
  candle_action296_grouped_32_marker "source-preparation" "end";;

let candle_action296_grouped_32_prepared () =
  match !candle_action296_grouped_32_prepared_ref with
  | Some prepared -> prepared
  | None -> failwith "action296 grouped 32: missing preparation";;

let _ =
  candle_action296_grouped_32_marker "point-plan-compilation" "begin";;
let candle_action296_grouped_32_plans_ref :
    (thm list * candle_q_dim_analytic_jet_prepared_six *
     candle_q_dim_taylor_model_point_plan_six) list option ref = ref None;;
let _ =
  candle_action296_grouped_32_plans_ref :=
    Some
      (map
        (fun (domains,prepared) ->
          domains,prepared,candle_q_dim_taylor_model_point_plan_six prepared)
        (candle_action296_grouped_32_prepared ()));;
let _ =
  candle_action296_grouped_32_marker "point-plan-compilation" "end";;

let candle_action296_grouped_32_plans () =
  match !candle_action296_grouped_32_plans_ref with
  | Some plans -> plans
  | None -> failwith "action296 grouped 32: missing point plans";;

let _ =
  candle_action296_grouped_32_marker "per-box-preparation" "begin";;
let candle_action296_grouped_32_jobs_ref :
    (candle_q_dim_analytic_jet_prepared_six *
     candle_action296_adaptive_grouping_case_six list) list option ref =
  ref None;;
let _ =
  candle_action296_grouped_32_jobs_ref :=
    Some
      (map
        (fun (domains,prepared,plan) ->
          prepared,
          map (candle_action296_adaptive_grouping_case prepared plan) domains)
        (candle_action296_grouped_32_plans ()));;
let _ =
  candle_action296_grouped_32_marker "per-box-preparation" "end";;

let candle_action296_grouped_32_jobs () =
  match !candle_action296_grouped_32_jobs_ref with
  | Some jobs -> jobs
  | None -> failwith "action296 grouped 32: missing jobs";;

let _ =
  candle_action296_grouped_32_marker "kernel-compute" "begin";;
let candle_action296_grouped_32_flags_ref : term list option ref = ref None;;
let _ =
  candle_action296_grouped_32_flags_ref :=
    Some
      (List.flatten
        (map candle_action296_adaptive_grouping_compute
          (candle_action296_grouped_32_jobs ())));;
let _ =
  candle_action296_grouped_32_marker "kernel-compute" "end";;

let candle_action296_grouped_32_flags () =
  match !candle_action296_grouped_32_flags_ref with
  | Some flags -> flags
  | None -> failwith "action296 grouped 32: missing flags";;

let candle_action296_grouped_32_flag_strings =
  map candle_action296_adaptive_grouping_flag_string
    (candle_action296_grouped_32_flags ());;

let candle_action296_grouped_32_accepted =
  List.fold_left
    (fun count flag -> if flag = "1" then count + 1 else count)
    0 candle_action296_grouped_32_flag_strings;;

let candle_action296_grouped_32_actual_group_sizes =
  map
    (fun (domains,_) -> string_of_int (length domains))
    (candle_action296_grouped_32_prepared ());;

let candle_action296_grouped_32_expected_group_sizes =
  ["4"; "4"; "4"; "2"; "2"; "4"; "2"; "2"; "4"; "1"; "1"; "2"];;

let candle_action296_grouped_32_expected_flags =
  ["0"; "0"; "0"; "0"; "1"; "1"; "1"; "1";
   "0"; "0"; "1"; "1"; "0"; "0"; "1"; "1";
   "0"; "0"; "0"; "0"; "0"; "0"; "0"; "0";
   "0"; "0"; "0"; "0"; "0"; "1"; "0"; "0"];;

if length candle_action296_grouped_32_groups <> 8 ||
   length (candle_action296_grouped_32_flags ()) <> 32 ||
   candle_action296_grouped_32_actual_group_sizes <>
     candle_action296_grouped_32_expected_group_sizes ||
   candle_action296_grouped_32_accepted <> 9 ||
   candle_action296_grouped_32_flag_strings <>
     candle_action296_grouped_32_expected_flags then
  failwith "action296 grouped 32: fixture identity or expected verdict";;

print_endline
  ("CANDLE_CV_ACTION296_GROUPED_32_ALGEBRAIC_RESULT" ^
   " leaves=32 requested_groups=8 actual_groups=" ^
   string_of_int (length (candle_action296_grouped_32_prepared ())) ^
   " group_sizes=" ^
   String.concat "," candle_action296_grouped_32_actual_group_sizes ^
   " accepted=" ^
   string_of_int candle_action296_grouped_32_accepted ^
   " flags=" ^ String.concat "," candle_action296_grouped_32_flag_strings);;
print_endline
  "CANDLE_CV_ACTION296_GROUPED_32_ALGEBRAIC_OK DEVELOPMENT_NON_RELEASE";;
