(* ========================================================================== *)
(* Adaptive grouping discriminator for the first eight genuine NL leaves.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Leaves 0--3 are split once on coordinate 4;   *)
(* leaves 4--7 remain intact.  Each consecutive group of four shares one      *)
(* outer box certificate and one aggregate tagged-algebraic evaluator call.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_leaf_grouping_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compute.ml";;

open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;

let candle_action296_adaptive_grouping_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-adaptive-grouping-algebraic" ^
     " scope=first-8 phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_adaptive_grouping_groups =
  candle_action296_leaf_grouping_partition 4
    candle_action296_leaf_grouping_domains;;

let candle_action296_adaptive_grouping_axis4_children domain_th =
  let left,right =
    M_verifier.split_domain candle_action296_plan_dimension 6 4 domain_th in
  [left;right];;

let candle_action296_adaptive_grouping_final_domains = function
  | [first_group;second_group] ->
      [List.flatten
         (map candle_action296_adaptive_grouping_axis4_children first_group);
       second_group]
  | _ -> failwith "action296 adaptive grouping: group shape";;

let candle_action296_adaptive_grouping_finals =
  candle_action296_adaptive_grouping_final_domains
    candle_action296_adaptive_grouping_groups;;

let candle_cv_action296_adaptive_grouping_flags_def = define
 `(candle_cv_action296_adaptive_grouping_flags
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_adaptive_grouping_flags
      box_program (Cexp_pair job jobs) =
     Cexp_pair
       (Cexp_fst
         (candle_cv_fsa_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_adaptive_grouping_flags box_program jobs))`;;

let candle_cv_action296_adaptive_grouping_flags_compute = prove
 (`!box_program jobs.
     candle_cv_action296_adaptive_grouping_flags box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (Cexp_fst
           (candle_cv_fsa_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_adaptive_grouping_flags
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_adaptive_grouping_flags_def;cexp_if_def;
              cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_action296_adaptive_grouping_eqs =
  union candle_cv_fsa_compute_eqs
    [SPEC_ALL candle_cv_action296_adaptive_grouping_flags_compute];;

let candle_action296_adaptive_grouping_case prepared plan domain_th =
  let lower,upper =
    candle_action296_leaf_grouping_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      prepared plan lower upper in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  list_mk_comb
    (`Cexp_pair`,
     [center_variant.variant_program_representation_term;
      rand (concl boxes_representation)]);;

let candle_action296_adaptive_grouping_cases_term cases =
  itlist
    (fun item tail -> list_mk_comb (`Cexp_pair`,[item;tail]))
    cases `Cexp_num 0`;;

let rec candle_action296_adaptive_grouping_dest_flags tm =
  if aconv tm `Cexp_num 0` then [] else
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [flag;tail] ->
        flag :: candle_action296_adaptive_grouping_dest_flags tail
    | _ -> failwith "action296 adaptive grouping: malformed flag pair"
  else failwith "action296 adaptive grouping: malformed flag list";;

let candle_action296_adaptive_grouping_compute (prepared,cases) =
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_action296_adaptive_grouping_eqs
      (list_mk_comb
        (`candle_cv_action296_adaptive_grouping_flags`,
         [prepared.program_representation_term;
          candle_action296_adaptive_grouping_cases_term cases])) in
  if hyp theorem <> [] then
    failwith "action296 adaptive grouping: computed theorem assumptions";
  let flags =
    candle_action296_adaptive_grouping_dest_flags (rand (concl theorem)) in
  if length flags <> length cases then
    failwith "action296 adaptive grouping: result cardinality";
  flags;;

let _ =
  candle_action296_adaptive_grouping_marker
    "source-preparation" "begin";;
let candle_action296_adaptive_grouping_prepared_ref :
    candle_q_dim_analytic_jet_prepared_six list option ref = ref None;;
let _ =
  candle_action296_adaptive_grouping_prepared_ref :=
    Some
      (map
        (fun domains ->
          let lower,upper =
            candle_action296_leaf_grouping_envelope domains in
          candle_q_dim_analytic_jet_prepare_box_six
            candle_action296_plan_prepared.function_term lower upper)
        candle_action296_adaptive_grouping_groups);;
let _ =
  candle_action296_adaptive_grouping_marker
    "source-preparation" "end";;

let candle_action296_adaptive_grouping_prepared () =
  match !candle_action296_adaptive_grouping_prepared_ref with
  | Some prepared -> prepared
  | None -> failwith "action296 adaptive grouping: missing preparation";;

let _ =
  candle_action296_adaptive_grouping_marker
    "point-plan-compilation" "begin";;
let candle_action296_adaptive_grouping_plans_ref :
    candle_q_dim_taylor_model_point_plan_six list option ref = ref None;;
let _ =
  candle_action296_adaptive_grouping_plans_ref :=
    Some
      (map candle_q_dim_taylor_model_point_plan_six
        (candle_action296_adaptive_grouping_prepared ()));;
let _ =
  candle_action296_adaptive_grouping_marker
    "point-plan-compilation" "end";;

let candle_action296_adaptive_grouping_plans () =
  match !candle_action296_adaptive_grouping_plans_ref with
  | Some plans -> plans
  | None -> failwith "action296 adaptive grouping: missing plans";;

let rec candle_action296_adaptive_grouping_map3 action left middle right =
  match left,middle,right with
  | [],[],[] -> []
  | left_head::left_tail,middle_head::middle_tail,right_head::right_tail ->
      action left_head middle_head right_head ::
      candle_action296_adaptive_grouping_map3
        action left_tail middle_tail right_tail
  | _ -> failwith "action296 adaptive grouping: group cardinality";;

let _ =
  candle_action296_adaptive_grouping_marker
    "per-box-preparation" "begin";;
let candle_action296_adaptive_grouping_jobs_ref :
    (candle_q_dim_analytic_jet_prepared_six * term list) list option ref =
  ref None;;
let _ =
  candle_action296_adaptive_grouping_jobs_ref :=
    Some
      (candle_action296_adaptive_grouping_map3
        (fun prepared plan domains ->
          prepared,
          map (candle_action296_adaptive_grouping_case prepared plan) domains)
        (candle_action296_adaptive_grouping_prepared ())
        (candle_action296_adaptive_grouping_plans ())
        candle_action296_adaptive_grouping_finals);;
let _ =
  candle_action296_adaptive_grouping_marker
    "per-box-preparation" "end";;

let candle_action296_adaptive_grouping_jobs () =
  match !candle_action296_adaptive_grouping_jobs_ref with
  | Some jobs -> jobs
  | None -> failwith "action296 adaptive grouping: missing jobs";;

let _ =
  candle_action296_adaptive_grouping_marker "kernel-compute" "begin";;
let candle_action296_adaptive_grouping_flags_ref :
    term list list option ref = ref None;;
let _ =
  candle_action296_adaptive_grouping_flags_ref :=
    Some
      (map candle_action296_adaptive_grouping_compute
        (candle_action296_adaptive_grouping_jobs ()));;
let _ =
  candle_action296_adaptive_grouping_marker "kernel-compute" "end";;

let candle_action296_adaptive_grouping_flags () =
  match !candle_action296_adaptive_grouping_flags_ref with
  | Some flags -> flags
  | None -> failwith "action296 adaptive grouping: missing flags";;

let candle_action296_adaptive_grouping_flag_string flag =
  if aconv flag `Cexp_num 1` then "1"
  else if aconv flag `Cexp_num 0` then "0"
  else failwith "action296 adaptive grouping: non-Boolean flag";;

let candle_action296_adaptive_grouping_flag_sets =
  map
    (fun flags ->
      String.concat ","
        (map candle_action296_adaptive_grouping_flag_string flags))
    (candle_action296_adaptive_grouping_flags ());;

print_endline
  ("CANDLE_CV_ACTION296_ADAPTIVE_GROUPING_ALGEBRAIC_RESULT" ^
   " group0_cells=8 group0_flags=" ^
   List.nth candle_action296_adaptive_grouping_flag_sets 0 ^
   " group1_cells=4 group1_flags=" ^
   List.nth candle_action296_adaptive_grouping_flag_sets 1);;

if length candle_action296_adaptive_grouping_groups <> 2 ||
   length candle_action296_adaptive_grouping_finals <> 2 ||
   length (List.nth candle_action296_adaptive_grouping_finals 0) <> 8 ||
   length (List.nth candle_action296_adaptive_grouping_finals 1) <> 4 then
  failwith "action296 adaptive grouping: final shape";;

print_endline
  "CANDLE_CV_ACTION296_ADAPTIVE_GROUPING_ALGEBRAIC_OK DEVELOPMENT_NON_RELEASE";;
