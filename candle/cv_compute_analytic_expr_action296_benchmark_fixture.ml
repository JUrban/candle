(* ========================================================================== *)
(* Lightweight genuine action-296 benchmark fixture.                         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This prepares the authenticated expression,   *)
(* eight distinct accepted subboxes, and small concrete-cval inspection      *)
(* helpers without replaying the separate 432-instruction profiling suite.   *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;

let candle_action296_instruction_profile_marker phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-benchmark-fixture scope=boxes-8" ^
     " phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_action296_instruction_profile_marker
    "shared-preparation" "begin";;

let candle_action296_instruction_profile_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_instruction_profile_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 fixture: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 fixture: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_instruction_profile_find left_domain left
  | P_result_mono _ ->
      failwith "action296 fixture: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 fixture: unexpected reference node";;

let candle_action296_instruction_profile_parent_domain =
  candle_action296_instruction_profile_find
    candle_action296_instruction_profile_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_instruction_profile_probe_domain,_ =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_instruction_profile_parent_domain;;

let candle_action296_instruction_profile_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let candle_action296_instruction_profile_probe_lower,
    candle_action296_instruction_profile_probe_upper =
  candle_action296_instruction_profile_domain_bounds
    candle_action296_instruction_profile_probe_domain;;

let candle_action296_instruction_profile_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_instruction_profile_probe_lower
    candle_action296_instruction_profile_probe_upper;;

let candle_action296_instruction_profile_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_instruction_profile_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_instruction_profile_subdivide remaining
        (List.flatten
          (map (candle_action296_instruction_profile_split axis) domains));;

let candle_action296_instruction_profile_domains =
  candle_action296_instruction_profile_subdivide [1;2;3]
    [candle_action296_instruction_profile_probe_domain];;

let candle_action296_instruction_profile_cases =
  map
    (fun domain_th ->
      let lower,upper =
        candle_action296_instruction_profile_domain_bounds domain_th in
      let variant =
        candle_q_dim_taylor_model_prepare_point_variant_six
          candle_action296_instruction_profile_box_prepared lower upper in
      variant,lower,upper)
    candle_action296_instruction_profile_domains;;

let _ =
  candle_action296_instruction_profile_marker
    "shared-preparation" "end";;

type candle_action296_instruction_profile_cval =
  | Candle_action296_instruction_num of num
  | Candle_action296_instruction_pair of term * term;;

let candle_action296_instruction_profile_view tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [argument] ->
        Candle_action296_instruction_num (dest_numeral argument)
    | _ -> failwith "action296 fixture: malformed Cexp_num"
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> Candle_action296_instruction_pair (left,right)
    | _ -> failwith "action296 fixture: malformed Cexp_pair"
  else failwith "action296 fixture: non-concrete cval";;

let rec candle_action296_instruction_profile_list tm =
  match candle_action296_instruction_profile_view tm with
  | Candle_action296_instruction_num n ->
      if Num.eq_num n (Num.num_of_int 0) then []
      else failwith "action296 fixture: malformed cval list tail"
  | Candle_action296_instruction_pair (head,tail) ->
      head :: candle_action296_instruction_profile_list tail;;

let candle_action296_instruction_profile_top stack =
  match candle_action296_instruction_profile_view stack with
  | Candle_action296_instruction_pair (head,_) -> head
  | Candle_action296_instruction_num _ ->
      failwith "action296 fixture: empty result stack";;

let candle_action296_instruction_profile_opcode instruction =
  match candle_action296_instruction_profile_view instruction with
  | Candle_action296_instruction_pair (tag,payload) ->
      (match candle_action296_instruction_profile_view tag with
       | Candle_action296_instruction_num n ->
           if Num.eq_num n (Num.num_of_int 0) then
             "poly",length (candle_action296_instruction_profile_list payload)
           else if Num.eq_num n (Num.num_of_int 1) then "sqrt",0
           else "pair-unknown",0
       | _ -> "pair-unknown",0)
  | Candle_action296_instruction_num n ->
      if Num.eq_num n (Num.num_of_int 2) then "neg",0
      else if Num.eq_num n (Num.num_of_int 3) then "add",0
      else if Num.eq_num n (Num.num_of_int 4) then "mul",0
      else if Num.eq_num n (Num.num_of_int 5) then "square",0
      else if Num.eq_num n (Num.num_of_int 6) then "inv",0
      else if Num.eq_num n (Num.num_of_int 7) then "atn",0
      else if Num.eq_num n (Num.num_of_int 8) then "pi-half",0
      else "num-unknown",0;;

let candle_action296_instruction_profile_arity opcode =
  if opcode = "poly" || opcode = "pi-half" then 0
  else if opcode = "neg" || opcode = "square" || opcode = "inv" ||
          opcode = "sqrt" || opcode = "atn" then 1
  else if opcode = "add" || opcode = "mul" then 2
  else failwith "action296 fixture: unknown opcode arity";;

let rec candle_action296_instruction_profile_term_stack = function
  | [] -> `Cexp_num 0`
  | head :: tail ->
      list_mk_comb
        (`Cexp_pair`,
         [head;candle_action296_instruction_profile_term_stack tail]);;

print_endline
  "CANDLE_CV_ACTION296_BENCHMARK_FIXTURE_OK boxes=8 DEVELOPMENT_NON_RELEASE";;
