(* ========================================================================== *)
(* Envelope-sharing discriminator for genuine action-296 certificate leaves. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE diagnostic.  The first eight adjacent precision *)
(* leaves are checked with one box certificate per leaf and with certificates *)
(* shared over consecutive groups of 2, 4, and 8 leaves.  Every group uses one *)
(* reflected call and returns only its fixed-hybrid acceptance flags.          *)
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

let candle_action296_leaf_grouping_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-leaf-grouping scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_leaf_grouping_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_leaf_grouping_collect domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 leaf grouping: unexpected pass selection";
      [domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 leaf grouping: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_leaf_grouping_collect left_domain left @
      candle_action296_leaf_grouping_collect right_domain right
  | P_result_mono _ ->
      failwith "action296 leaf grouping: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 leaf grouping: unexpected reference node";;

let candle_action296_leaf_grouping_leaves : thm list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_leaves :=
    candle_action296_leaf_grouping_collect
      candle_action296_leaf_grouping_root_domain
      candle_action296_plan_precision_tree;;

if length !candle_action296_leaf_grouping_leaves <> 1061 then
  failwith "action296 leaf grouping: leaf cardinality drift";;

let candle_action296_leaf_grouping_indices = [0;1;2;3;4;5;6;7];;
let candle_action296_leaf_grouping_domains =
  map
    (fun index -> List.nth !candle_action296_leaf_grouping_leaves index)
    candle_action296_leaf_grouping_indices;;

let candle_action296_leaf_grouping_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_leaf_grouping_envelope_lower left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then l else r)
    left right;;

let candle_action296_leaf_grouping_envelope_upper left right =
  map2
    (fun l r -> if Num.le_num (rat_of_term l) (rat_of_term r) then r else l)
    left right;;

let candle_action296_leaf_grouping_envelope domains =
  match map candle_action296_leaf_grouping_domain_bounds domains with
  | first :: remaining ->
      List.fold_left
        (fun (lower,upper) (next_lower,next_upper) ->
          candle_action296_leaf_grouping_envelope_lower lower next_lower,
          candle_action296_leaf_grouping_envelope_upper upper next_upper)
        first remaining
  | [] -> failwith "action296 leaf grouping: empty envelope";;

let rec candle_action296_leaf_grouping_take count items =
  if count = 0 then [],items else
  match items with
  | [] -> failwith "action296 leaf grouping: incomplete group"
  | head :: tail ->
      let selected,remaining =
        candle_action296_leaf_grouping_take (count - 1) tail in
      head :: selected,remaining;;

let rec candle_action296_leaf_grouping_partition group_size items =
  match items with
  | [] -> []
  | _ ->
      let group,remaining =
        candle_action296_leaf_grouping_take group_size items in
      group ::
        candle_action296_leaf_grouping_partition group_size remaining;;

let candle_cv_action296_leaf_grouping_flags_def = define
 `(candle_cv_action296_leaf_grouping_flags
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_leaf_grouping_flags
      box_program (Cexp_pair job jobs) =
     Cexp_pair
       (Cexp_fst
         (candle_cv_fs_q_dim_taylor_model_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_leaf_grouping_flags box_program jobs))`;;

let candle_cv_action296_leaf_grouping_flags_compute = prove
 (`!box_program jobs.
     candle_cv_action296_leaf_grouping_flags box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_pair
         (Cexp_fst
           (candle_cv_fs_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_leaf_grouping_flags
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_leaf_grouping_flags_def;cexp_if_def;
              cexp_ispair_def;cexp_fst_def;cexp_snd_def]);;

let candle_action296_leaf_grouping_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    [SPEC_ALL candle_cv_action296_leaf_grouping_flags_compute];;

let candle_action296_leaf_grouping_case prepared plan domain_th =
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

let candle_action296_leaf_grouping_cases_term cases =
  itlist
    (fun item tail -> list_mk_comb (`Cexp_pair`,[item;tail]))
    cases `Cexp_num 0`;;

let rec candle_action296_leaf_grouping_dest_flags tm =
  if aconv tm `Cexp_num 0` then []
  else
    let operator,arguments = strip_comb tm in
    if aconv operator `Cexp_pair` then
      match arguments with
      | [flag;tail] ->
          flag :: candle_action296_leaf_grouping_dest_flags tail
      | _ -> failwith "action296 leaf grouping: malformed flag pair"
    else failwith "action296 leaf grouping: malformed flag list";;

let candle_action296_leaf_grouping_compute (prepared,cases) =
  let theorem =
    candle_q_dim_analytic_jet_compute
      candle_action296_leaf_grouping_eqs
      (list_mk_comb
        (`candle_cv_action296_leaf_grouping_flags`,
         [prepared.program_representation_term;
          candle_action296_leaf_grouping_cases_term cases])) in
  if hyp theorem <> [] then
    failwith "action296 leaf grouping: computed theorem assumptions";
  let flags =
    candle_action296_leaf_grouping_dest_flags (rand (concl theorem)) in
  if length flags <> length cases then
    failwith "action296 leaf grouping: result cardinality";
  flags;;

let candle_action296_leaf_grouping_flag_string flag =
  if aconv flag `Cexp_num 1` then "1"
  else if aconv flag `Cexp_num 0` then "0"
  else failwith "action296 leaf grouping: non-Boolean result";;

let candle_action296_leaf_grouping_run group_size =
  if group_size <= 0 || 8 mod group_size <> 0 then
    failwith "action296 leaf grouping: invalid group size";
  let scope = "group-" ^ string_of_int group_size in
  let groups =
    candle_action296_leaf_grouping_partition group_size
      candle_action296_leaf_grouping_domains in
  candle_action296_leaf_grouping_marker scope "source-preparation" "begin";
  let prepared_groups =
    map
      (fun domains ->
        let lower,upper = candle_action296_leaf_grouping_envelope domains in
        domains,
        candle_q_dim_analytic_jet_prepare_box_six
          candle_action296_plan_prepared.function_term lower upper)
      groups in
  candle_action296_leaf_grouping_marker scope "source-preparation" "end";
  candle_action296_leaf_grouping_marker scope "point-plan-compilation" "begin";
  let planned_groups =
    map
      (fun (domains,prepared) ->
        domains,prepared,candle_q_dim_taylor_model_point_plan_six prepared)
      prepared_groups in
  candle_action296_leaf_grouping_marker scope "point-plan-compilation" "end";
  candle_action296_leaf_grouping_marker scope "per-box-preparation" "begin";
  let computed_groups =
    map
      (fun (domains,prepared,plan) ->
        prepared,
        map (candle_action296_leaf_grouping_case prepared plan) domains)
      planned_groups in
  candle_action296_leaf_grouping_marker scope "per-box-preparation" "end";
  candle_action296_leaf_grouping_marker scope "kernel-compute" "begin";
  let flags =
    List.flatten (map candle_action296_leaf_grouping_compute computed_groups) in
  candle_action296_leaf_grouping_marker scope "kernel-compute" "end";
  if length groups <> 8 / group_size || length flags <> 8 then
    failwith "action296 leaf grouping: aggregate cardinality";
  let flag_strings = map candle_action296_leaf_grouping_flag_string flags in
  let accepted =
    List.fold_left
      (fun count flag -> if flag = "1" then count + 1 else count)
      0 flag_strings in
  print_endline
    ("CANDLE_CV_ACTION296_LEAF_GROUPING_RESULT group_size=" ^
     string_of_int group_size ^ " groups=" ^ string_of_int (length groups) ^
     " accepted=" ^ string_of_int accepted ^ " flags=" ^
     String.concat "," flag_strings);
  flags;;

let candle_action296_leaf_grouping_flags_1 : term list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_flags_1 :=
    candle_action296_leaf_grouping_run 1;;
let candle_action296_leaf_grouping_flags_2 : term list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_flags_2 :=
    candle_action296_leaf_grouping_run 2;;
let candle_action296_leaf_grouping_flags_4 : term list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_flags_4 :=
    candle_action296_leaf_grouping_run 4;;
let candle_action296_leaf_grouping_flags_8 : term list ref = ref [];;
let _ =
  candle_action296_leaf_grouping_flags_8 :=
    candle_action296_leaf_grouping_run 8;;

print_endline
  "CANDLE_CV_ACTION296_LEAF_GROUPING_OK DEVELOPMENT_NON_RELEASE";;
