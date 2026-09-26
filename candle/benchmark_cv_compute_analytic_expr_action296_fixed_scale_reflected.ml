(* ========================================================================== *)
(* Scaling benchmark for the reflected fixed-scale polynomial backend.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Genuine action-296 blocks 32 and 33 are run   *)
(* on one and 64 distinct subboxes.  The 64-box fixed-scale batch is executed *)
(* before the established rational batch, reversing the order of the earlier *)
(* eight-box experiment.  Every complete result must remain structurally     *)
(* identical.                                                                *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_compute.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_compute.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;
open Candle_cv_analytic_expr_fixed_scale_compute;;

let candle_action296_fs_reflected_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fs-reflected scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fs_reflected_compute equations tm =
  candle_q_dim_analytic_jet_compute equations tm;;

(* Compact batch outputs exercise the intended checker boundary: numerical   *)
(* intermediates stay inside Kernel.compute and only one aggregate numeral   *)
(* crosses back into the theorem.  Full outputs are still compared below,    *)
(* one case at a time.                                                        *)

let candle_cv_fs_reflected_fixed_checksum_def = new_definition
 `candle_cv_fs_reflected_fixed_checksum result =
    Cexp_add
      (Cexp_fst
        (Cexp_snd (candle_cv_fs_result_value_bound result)))
      (Cexp_snd
        (Cexp_snd (candle_cv_fs_result_value_bound result)))`;;

let candle_cv_fs_reflected_current_checksum_def = new_definition
 `candle_cv_fs_reflected_current_checksum result =
    Cexp_add
      (Cexp_fst
        (Cexp_fst
          (Cexp_snd
            (candle_cv_q_dim_taylor_model_result_value_bound result))))
      (Cexp_snd
        (Cexp_fst
          (Cexp_snd
            (candle_cv_q_dim_taylor_model_result_value_bound result))))`;;

let candle_cv_fs_reflected_fixed_batch_def = define
 `(candle_cv_fs_reflected_fixed_batch program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_reflected_fixed_batch program (Cexp_pair h t) =
     Cexp_add
       (candle_cv_fs_reflected_fixed_checksum
         (candle_cv_fs_poly_program
           (Cexp_fst h) (Cexp_snd (Cexp_snd h)) program))
       (candle_cv_fs_reflected_fixed_batch program t))`;;

let candle_cv_fs_reflected_fixed_batch_compute = prove
 (`!program cases.
     candle_cv_fs_reflected_fixed_batch program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_add
         (candle_cv_fs_reflected_fixed_checksum
           (candle_cv_fs_poly_program
             (Cexp_fst (Cexp_fst cases))
             (Cexp_snd (Cexp_snd (Cexp_fst cases))) program))
         (candle_cv_fs_reflected_fixed_batch program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_reflected_fixed_batch_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_fs_reflected_current_batch_def = define
 `(candle_cv_fs_reflected_current_batch program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_fs_reflected_current_batch program (Cexp_pair h t) =
     Cexp_add
       (candle_cv_fs_reflected_current_checksum
         (candle_cv_q_dim_taylor_model_poly_program
           (Cexp_fst h) (Cexp_fst (Cexp_snd h))
           (Cexp_snd (Cexp_snd h)) program))
       (candle_cv_fs_reflected_current_batch program t))`;;

let candle_cv_fs_reflected_current_batch_compute = prove
 (`!program cases.
     candle_cv_fs_reflected_current_batch program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_add
         (candle_cv_fs_reflected_current_checksum
           (candle_cv_q_dim_taylor_model_poly_program
             (Cexp_fst (Cexp_fst cases))
             (Cexp_fst (Cexp_snd (Cexp_fst cases)))
             (Cexp_snd (Cexp_snd (Cexp_fst cases))) program))
         (candle_cv_fs_reflected_current_batch program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_reflected_current_batch_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_action296_fs_reflected_equations =
  union candle_cv_fs_compute_eqs
    (map SPEC_ALL
      [candle_cv_fs_reflected_fixed_checksum_def;
       candle_cv_fs_reflected_current_checksum_def;
       candle_cv_fs_reflected_fixed_batch_compute;
       candle_cv_fs_reflected_current_batch_compute]);;

let candle_action296_fs_reflected_domain_bounds domain_th =
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  lower,upper;;

let rec candle_action296_fs_reflected_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 reflected fixed: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 reflected fixed: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_fs_reflected_find left_domain left
  | P_result_mono _ ->
      failwith "action296 reflected fixed: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 reflected fixed: unexpected reference node";;

let candle_action296_fs_reflected_split axis domain_th =
  let left,right =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 axis domain_th in
  [left;right];;

let rec candle_action296_fs_reflected_subdivide axes domains =
  match axes with
  | [] -> domains
  | axis :: remaining ->
      candle_action296_fs_reflected_subdivide remaining
        (List.flatten
          (map (candle_action296_fs_reflected_split axis) domains));;

type candle_action296_fs_reflected_case = {
  candle_action296_fs_reflected_boxes: term;
  candle_action296_fs_reflected_center_boxes: term;
  candle_action296_fs_reflected_radii: term
};;

let candle_action296_fs_reflected_nth index items =
  let rec find remaining = function
    | [] -> failwith "action296 reflected fixed: instruction outside program"
    | head :: tail -> if remaining = 0 then head else find (remaining - 1) tail in
  find index items;;

let candle_action296_fs_reflected_pair tm =
  let operator,arguments = strip_comb tm in
  if not (aconv operator `Cexp_pair`) then
    failwith "action296 reflected fixed: expected pair";
  match arguments with
  | [left;right] -> left,right
  | _ -> failwith "action296 reflected fixed: malformed pair";;

let rec candle_action296_fs_reflected_list tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then []
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] -> head :: candle_action296_fs_reflected_list tail
    | _ -> failwith "action296 reflected fixed: malformed list"
  else failwith "action296 reflected fixed: non-concrete list";;

let candle_action296_fs_reflected_poly_payload instruction =
  let tag,payload = candle_action296_fs_reflected_pair instruction in
  if not (aconv tag `Cexp_num 0`) then
    failwith "action296 reflected fixed: expected polynomial block";
  payload;;

let candle_action296_fs_reflected_make_case domain_th =
  let lower,upper = candle_action296_fs_reflected_domain_bounds domain_th in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_term = rand (concl boxes_representation) in
  let center_th =
    candle_action296_fs_reflected_compute
      candle_cv_q_dim_taylor_model_certified_compute_eqs
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_term)) in
  let radii_th =
    candle_action296_fs_reflected_compute
      candle_cv_q_dim_taylor_model_certified_compute_eqs
      (mk_comb
        (`candle_cv_q_fixed_list_round_upper`,
         mk_comb (`candle_cv_q_radius_list`,boxes_term))) in
  if hyp center_th <> [] || hyp radii_th <> [] then
    failwith "action296 reflected fixed: setup assumptions";
  {candle_action296_fs_reflected_boxes = boxes_term;
   candle_action296_fs_reflected_center_boxes = rand (concl center_th);
   candle_action296_fs_reflected_radii = rand (concl radii_th)};;

let candle_action296_fs_reflected_run_fixed case block =
  candle_action296_fs_reflected_compute candle_cv_fs_compute_eqs
    (list_mk_comb
      (`candle_cv_fs_poly_program_to_q`,
       [case.candle_action296_fs_reflected_center_boxes;
        case.candle_action296_fs_reflected_radii;block]));;

let candle_action296_fs_reflected_run_current case block =
  candle_action296_fs_reflected_compute
    candle_cv_q_dim_taylor_model_certified_compute_eqs
    (list_mk_comb
      (`candle_cv_q_dim_taylor_model_poly_program`,
       [case.candle_action296_fs_reflected_center_boxes;
        case.candle_action296_fs_reflected_boxes;
        case.candle_action296_fs_reflected_radii;block]));;

let candle_action296_fs_reflected_case_term case =
  list_mk_comb
    (`Cexp_pair`,
     [case.candle_action296_fs_reflected_center_boxes;
      list_mk_comb
        (`Cexp_pair`,
         [case.candle_action296_fs_reflected_boxes;
          case.candle_action296_fs_reflected_radii])]);;

let candle_action296_fs_reflected_cases_term cases =
  itlist
    (fun case tail ->
      list_mk_comb
        (`Cexp_pair`,
         [candle_action296_fs_reflected_case_term case;tail]))
    cases `Cexp_num 0`;;

let candle_action296_fs_reflected_run () =
  let axioms_before = axioms () in
  candle_action296_fs_reflected_marker "batch" "profiled-run" "begin";
  let root_domain =
    M_taylor.mk_m_center_domain
      candle_action296_plan_dimension 6
      candle_action296_plan_xx1 candle_action296_plan_zz1 in
  let parent_domain =
    candle_action296_fs_reflected_find
      root_domain candle_action296_plan_precision_tree in
  let probe_domain,_ =
    M_verifier.split_domain
      candle_action296_plan_dimension 6 4 parent_domain in
  let probe_lower,probe_upper =
    candle_action296_fs_reflected_domain_bounds probe_domain in
  candle_action296_fs_reflected_marker
    "shared" "whole-box-source-preparation" "begin";
  let box_prepared =
    candle_q_dim_analytic_jet_prepare_box_six
      candle_action296_plan_prepared.function_term probe_lower probe_upper in
  candle_action296_fs_reflected_marker
    "shared" "whole-box-source-preparation" "end";
  let top_program =
    candle_action296_fs_reflected_list box_prepared.program_representation_term in
  if length top_program <> 54 then
    failwith "action296 reflected fixed: top program cardinality";
  let block32 =
    candle_action296_fs_reflected_poly_payload
      (candle_action296_fs_reflected_nth 32 top_program) and
      block33 =
        candle_action296_fs_reflected_poly_payload
          (candle_action296_fs_reflected_nth 33 top_program) in
  let domains64 =
    candle_action296_fs_reflected_subdivide [1;2;3;1;2;3] [probe_domain] in
  if length domains64 <> 64 then
    failwith "action296 reflected fixed: 64-box cardinality";
  candle_action296_fs_reflected_marker "boxes-64" "box-setup" "begin";
  let cases64 = map candle_action296_fs_reflected_make_case domains64 in
  candle_action296_fs_reflected_marker "boxes-64" "box-setup" "end";
  let case1 = hd cases64 in
  let cases64_term = candle_action296_fs_reflected_cases_term cases64 in
  candle_action296_fs_reflected_marker "boxes-1" "reflected-fixed" "begin";
  let reflected1 =
    candle_action296_fs_reflected_run_fixed case1 block32,
    candle_action296_fs_reflected_run_fixed case1 block33 in
  candle_action296_fs_reflected_marker "boxes-1" "reflected-fixed" "end";
  candle_action296_fs_reflected_marker "boxes-1" "current-rational" "begin";
  let current1 =
    candle_action296_fs_reflected_run_current case1 block32,
    candle_action296_fs_reflected_run_current case1 block33 in
  candle_action296_fs_reflected_marker "boxes-1" "current-rational" "end";
  candle_action296_fs_reflected_marker
    "boxes-64" "reflected-fixed-compact" "begin";
  let reflected64 =
    candle_action296_fs_reflected_compute
      candle_action296_fs_reflected_equations
      (list_mk_comb
        (`candle_cv_fs_reflected_fixed_batch`,[block32;cases64_term])),
    candle_action296_fs_reflected_compute
      candle_action296_fs_reflected_equations
      (list_mk_comb
        (`candle_cv_fs_reflected_fixed_batch`,[block33;cases64_term])) in
  candle_action296_fs_reflected_marker
    "boxes-64" "reflected-fixed-compact" "end";
  candle_action296_fs_reflected_marker
    "boxes-64" "current-rational-compact" "begin";
  let current64 =
    candle_action296_fs_reflected_compute
      candle_action296_fs_reflected_equations
      (list_mk_comb
        (`candle_cv_fs_reflected_current_batch`,[block32;cases64_term])),
    candle_action296_fs_reflected_compute
      candle_action296_fs_reflected_equations
      (list_mk_comb
        (`candle_cv_fs_reflected_current_batch`,[block33;cases64_term])) in
  candle_action296_fs_reflected_marker
    "boxes-64" "current-rational-compact" "end";
  let validate_pair (fixed_left,fixed_right) (old_left,old_right) =
    hyp fixed_left = [] && hyp fixed_right = [] &&
    hyp old_left = [] && hyp old_right = [] &&
    aconv (rand (concl fixed_left)) (rand (concl old_left)) &&
    aconv (rand (concl fixed_right)) (rand (concl old_right)) in
  candle_action296_fs_reflected_marker
    "boxes-64" "streamed-exact-comparison" "begin";
  let rec validate count = function
    | [] -> count
    | case :: remaining ->
        let fixed_pair =
          candle_action296_fs_reflected_run_fixed case block32,
          candle_action296_fs_reflected_run_fixed case block33 in
        let old_pair =
          candle_action296_fs_reflected_run_current case block32,
          candle_action296_fs_reflected_run_current case block33 in
        if not (validate_pair fixed_pair old_pair) then
          failwith "action296 reflected fixed: exact result mismatch";
        validate (count + 2) remaining in
  let exact1 = if validate_pair reflected1 current1 then 2 else 0 and
      exact64 = validate 0 cases64 in
  candle_action296_fs_reflected_marker
    "boxes-64" "streamed-exact-comparison" "end";
  let axioms_after = axioms () in
  if exact1 <> 2 || exact64 <> 128 ||
     hyp (fst reflected64) <> [] || hyp (snd reflected64) <> [] ||
     hyp (fst current64) <> [] || hyp (snd current64) <> [] ||
     not
       (aconv (rand (concl (fst reflected64)))
              (rand (concl (fst current64)))) ||
     not
       (aconv (rand (concl (snd reflected64)))
              (rand (concl (snd current64)))) ||
     length axioms_after <> length axioms_before ||
     not
       (List.for_all
         (fun theorem -> List.mem theorem axioms_before) axioms_after) then
    failwith "action296 reflected fixed: final validation";
  candle_action296_fs_reflected_marker "batch" "profiled-run" "end";
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_SCALE_REFLECTED_RESULT boxes=1,64" ^
     " blocks=2 instructions=39,85 exact_outputs=" ^
     string_of_int (exact1 + exact64));
  print_endline
    "CANDLE_CV_ACTION296_FIXED_SCALE_REFLECTED_OK DEVELOPMENT_NON_RELEASE";;

let _ = candle_action296_fs_reflected_run ();;
