(* ========================================================================== *)
(* Complete certified centered proof of the first genuine action-296 leaf.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  One split along coordinate four gives two     *)
(* boxes accepted by the outward-rounded program checker.  The child source  *)
(* theorems are glued back to the original certificate leaf interface.       *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;

let candle_action296_certified_taylor_axioms_before = axioms ();;

let candle_action296_certified_taylor_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_certified_taylor_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 certified Taylor: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 certified Taylor: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_certified_taylor_find left_domain left
  | P_result_mono _ ->
      failwith "action296 certified Taylor: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 certified Taylor: unexpected reference node";;

let candle_action296_certified_taylor_parent_domain =
  candle_action296_certified_taylor_find
    candle_action296_certified_taylor_root_domain
    candle_action296_plan_precision_tree;;

let candle_action296_certified_taylor_left_domain,
    candle_action296_certified_taylor_right_domain =
  M_verifier.split_domain candle_action296_plan_dimension 6 4
    candle_action296_certified_taylor_parent_domain;;

let candle_action296_certified_taylor_variable_sqrt_intervals =
 [`((((47,0),19),((241,0),99)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((2047,0),999)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`;
  `((((199999,0),99999),((1033,0),499)):
     ((num#num)#num)#((num#num)#num))`];;

let candle_action296_certified_taylor_box_sqrt_interval tm =
  let rec choose variables intervals =
    match variables,intervals with
    | variable :: variable_tail,interval :: interval_tail ->
        if aconv tm variable then interval
        else choose variable_tail interval_tail
    | [],[] ->
        `((((38,0),0),((80,0),0)):
          ((num#num)#num)#((num#num)#num))`
    | _ -> failwith "action296 certified Taylor: sqrt interval shape" in
  choose candle_action296_plan_sqrt_variables
    candle_action296_certified_taylor_variable_sqrt_intervals;;

let candle_action296_certified_taylor_box_prepared =
  candle_q_dim_analytic_jet_prepare_six_with
    candle_action296_certified_taylor_box_sqrt_interval
    candle_action296_plan_prepared.function_term;;

let candle_action296_certified_taylor_profile_events : string list ref =
  ref [];;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_certified_taylor_profile_events :=
        event :: !candle_action296_certified_taylor_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_TAYLOR_STAGE event=" ^ event));;

let candle_action296_certified_taylor_prove label domain_th =
  let started = Unix.gettimeofday () in
  print_endline
    ("CANDLE_CV_ACTION296_CERTIFIED_TAYLOR_CELL cell=" ^ label ^
     " event=begin");
  let theorem =
    candle_reflected_nl_source_pass_with
      candle_action296_plan_prepared.function_term
      (fun lower upper ->
        let center_prepared =
          candle_q_dim_analytic_jet_prepare_point_six
            candle_action296_plan_prepared.function_term lower upper in
        candle_q_dim_taylor_model_certified_prove_box_six
          center_prepared candle_action296_certified_taylor_box_prepared
          lower upper)
      domain_th in
  print_endline
    ("CANDLE_CV_ACTION296_CERTIFIED_TAYLOR_CELL cell=" ^ label ^
     " event=end seconds=" ^
     string_of_float (Unix.gettimeofday () -. started));
  theorem;;

let candle_action296_certified_taylor_left_theorem =
  candle_action296_certified_taylor_prove "left"
    candle_action296_certified_taylor_left_domain;;

let candle_action296_certified_taylor_right_theorem =
  candle_action296_certified_taylor_prove "right"
    candle_action296_certified_taylor_right_domain;;

let candle_action296_certified_taylor_theorem =
  M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
    (M_verifier.m_glue_cells_list
      candle_action296_plan_dimension 4
      candle_action296_certified_taylor_left_theorem
      candle_action296_certified_taylor_right_theorem);;

let candle_action296_certified_taylor_functions,
    candle_action296_certified_taylor_proved_domain =
  M_verifier.dest_m_cell_list_pass
    (concl candle_action296_certified_taylor_theorem);;

let candle_action296_certified_taylor_expected_domain,_,_ =
  M_taylor.dest_m_cell_domain
    (concl candle_action296_certified_taylor_parent_domain);;

if candle_action296_certified_taylor_functions <>
     [candle_action296_plan_prepared.function_term] ||
   not
     (aconv candle_action296_certified_taylor_proved_domain
       candle_action296_certified_taylor_expected_domain) ||
   hyp candle_action296_certified_taylor_theorem <> [] then
  failwith "action296 certified Taylor: final theorem mismatch";;

let candle_action296_certified_taylor_axioms_after = axioms ();;

if length candle_action296_certified_taylor_axioms_after <>
     length candle_action296_certified_taylor_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_certified_taylor_axioms_before)
       candle_action296_certified_taylor_axioms_after) then
  failwith "action296 certified Taylor: changed global axiom set";;

print_endline
  ("CANDLE_CV_ACTION296_CERTIFIED_TAYLOR_RESULT cells=2" ^
   " profile_events=" ^
   string_of_int (length !candle_action296_certified_taylor_profile_events) ^
   " theorem_md5=" ^
   Digest.to_hex
     (Digest.string
       (string_of_thm candle_action296_certified_taylor_theorem)));
print_endline "CANDLE_CV_ACTION296_CERTIFIED_TAYLOR_OK DEVELOPMENT_NON_RELEASE";;
