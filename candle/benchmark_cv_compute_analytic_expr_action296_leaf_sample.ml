(* ========================================================================== *)
(* Eight-leaf sample from the genuine 1,061-leaf action-296 certificate.      *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  A box expression prepared over the *)
(* local envelope and one point plan are shared across eight adjacent pass    *)
(* leaves.  One reflected call returns every fixed-hybrid acceptance flag;    *)
(* rejection is informative here because this measures subdivision demand.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

let candle_action296_leaf_sample_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf-sample scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf_sample_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_leaf_sample_collect domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 leaf sample: unexpected pass selection";
      [domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 leaf sample: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_leaf_sample_collect left_domain left @
      candle_action296_leaf_sample_collect right_domain right
  | P_result_mono _ ->
      failwith "action296 leaf sample: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 leaf sample: unexpected reference node";;

let candle_action296_leaf_sample_leaves : thm list ref = ref [];;
let _ =
  candle_action296_leaf_sample_leaves :=
    candle_action296_leaf_sample_collect
      candle_action296_leaf_sample_root_domain
      candle_action296_plan_precision_tree;;

if length !candle_action296_leaf_sample_leaves <> 1061 then
  failwith "action296 leaf sample: leaf cardinality drift";;

let candle_action296_leaf_sample_indices = [0;1;2;3;4;5;6;7];;
let candle_action296_leaf_sample_domains =
  map
    (fun index -> List.nth !candle_action296_leaf_sample_leaves index)
    candle_action296_leaf_sample_indices;;

let candle_action296_leaf_sample_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_leaf_sample_bounds =
  map candle_action296_leaf_sample_domain_bounds
    candle_action296_leaf_sample_domains;;

let candle_action296_leaf_sample_envelope_lower left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then l else r)
    left right;;

let candle_action296_leaf_sample_envelope_upper left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then r else l)
    left right;;

let candle_action296_leaf_sample_envelope_lower_terms,
    candle_action296_leaf_sample_envelope_upper_terms =
  match candle_action296_leaf_sample_bounds with
  | first :: remaining ->
      List.fold_left
        (fun (lower,upper) (next_lower,next_upper) ->
          candle_action296_leaf_sample_envelope_lower lower next_lower,
          candle_action296_leaf_sample_envelope_upper upper next_upper)
        first remaining
  | [] -> failwith "action296 leaf sample: empty sample";;

let _ =
  candle_action296_leaf_sample_marker
    "shared" "local-envelope-source-preparation" "begin";;
let candle_action296_leaf_sample_box_prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term
    candle_action296_leaf_sample_envelope_lower_terms
    candle_action296_leaf_sample_envelope_upper_terms;;
let _ =
  candle_action296_leaf_sample_marker
    "shared" "local-envelope-source-preparation" "end";;

let _ =
  candle_action296_leaf_sample_marker
    "shared" "point-plan-compilation" "begin";;
let candle_action296_leaf_sample_point_plan =
  candle_q_dim_taylor_model_point_plan_six
    candle_action296_leaf_sample_box_prepared;;
let _ =
  candle_action296_leaf_sample_marker
    "shared" "point-plan-compilation" "end";;

let candle_action296_leaf_sample_case domain_th =
  let lower,upper = candle_action296_leaf_sample_domain_bounds domain_th in
  let center_variant =
    candle_q_dim_taylor_model_prepare_point_variant_with_plan_six
      candle_action296_leaf_sample_box_prepared
      candle_action296_leaf_sample_point_plan lower upper in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  list_mk_comb
    (`Cexp_pair`,
     [center_variant.variant_program_representation_term;
      rand (concl boxes_representation)]);;

let _ =
  candle_action296_leaf_sample_marker
    "boxes-8" "per-box-preparation" "begin";;
let candle_action296_leaf_sample_cases =
  map candle_action296_leaf_sample_case
    candle_action296_leaf_sample_domains;;
let _ =
  candle_action296_leaf_sample_marker
    "boxes-8" "per-box-preparation" "end";;

let candle_action296_leaf_sample_cases_term =
  itlist
    (fun item tail -> list_mk_comb (`Cexp_pair`,[item;tail]))
    candle_action296_leaf_sample_cases `Cexp_num 0`;;

let candle_cv_action296_leaf_sample_flags_def = define
 `(candle_cv_action296_leaf_sample_flags
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_leaf_sample_flags
      box_program (Cexp_pair job jobs) =
     Cexp_pair
       (Cexp_fst
         (candle_cv_fs_q_dim_taylor_model_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_leaf_sample_flags box_program jobs))`;;

let candle_cv_action296_leaf_sample_flags_compute = prove
 (`!box_program jobs.
     candle_cv_action296_leaf_sample_flags box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (Cexp_fst
           (candle_cv_fs_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_leaf_sample_flags
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_leaf_sample_flags_def;cexp_if_def;
              cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_action296_leaf_sample_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    [SPEC_ALL candle_cv_action296_leaf_sample_flags_compute];;

let _ =
  candle_action296_leaf_sample_marker
    "boxes-8" "kernel-compute" "begin";;
let candle_action296_leaf_sample_theorem =
  candle_q_dim_analytic_jet_compute
    candle_action296_leaf_sample_eqs
    (list_mk_comb
      (`candle_cv_action296_leaf_sample_flags`,
       [candle_action296_leaf_sample_box_prepared.
          program_representation_term;
        candle_action296_leaf_sample_cases_term]));;
let _ =
  candle_action296_leaf_sample_marker
    "boxes-8" "kernel-compute" "end";;

let rec candle_action296_leaf_sample_dest_flags tm =
  if aconv tm `Cexp_num 0` then []
  else
    let operator,arguments = strip_comb tm in
    if aconv operator `Cexp_pair` then
      match arguments with
      | [flag;tail] -> flag :: candle_action296_leaf_sample_dest_flags tail
      | _ -> failwith "action296 leaf sample: malformed flag pair"
    else failwith "action296 leaf sample: malformed flag list";;

let candle_action296_leaf_sample_flags =
  candle_action296_leaf_sample_dest_flags
    (rand (concl candle_action296_leaf_sample_theorem));;
let candle_action296_leaf_sample_accepted =
  List.fold_left
    (fun count flag ->
      if aconv flag `Cexp_num 1` then count + 1
      else if aconv flag `Cexp_num 0` then count
      else failwith "action296 leaf sample: non-Boolean result")
    0 candle_action296_leaf_sample_flags;;

if hyp candle_action296_leaf_sample_theorem <> [] ||
   length candle_action296_leaf_sample_flags <> 8 then
  failwith "action296 leaf sample: result mismatch";;

print_endline
  ("CANDLE_CV_ACTION296_LEAF_SAMPLE_RESULT total=8 accepted=" ^
   string_of_int candle_action296_leaf_sample_accepted ^
   " indices=" ^
   String.concat "," (map string_of_int candle_action296_leaf_sample_indices) ^
   " flags=" ^
   String.concat ","
     (map
       (fun flag -> if aconv flag `Cexp_num 1` then "1" else "0")
       candle_action296_leaf_sample_flags));;
print_endline
  "CANDLE_CV_ACTION296_LEAF_SAMPLE_OK DEVELOPMENT_NON_RELEASE";;
