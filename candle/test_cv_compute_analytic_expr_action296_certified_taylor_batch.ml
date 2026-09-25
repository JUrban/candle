(* ========================================================================== *)
(* Certified centered Taylor-model proofs for four genuine action-296 leaves. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The authenticated source program and its      *)
(* whole-box analytic certificates are prepared once.  Each selected leaf is *)
(* checked as data and subdivided only when the certified upper bound rejects *)
(* the original box.                                                          *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_plan.ml";;
needs "candle/cv_compute_analytic_expr_point_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_box_certificate_prepare.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_certified_prove.ml";;
needs "candle/cv_compute_analytic_expr_certificate_variant_prepare.ml";;

open Certificate;;
open M_verifier_build;;
open Candle_cv_flyspeck_nonlinear_driver;;
open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_action296_plan;;
open Candle_cv_analytic_expr_point_certificate_prepare;;
open Candle_cv_analytic_expr_box_certificate_prepare;;
open Candle_cv_analytic_expr_taylor_model_certified_prove;;
open Candle_cv_analytic_expr_certificate_variant_prepare;;

let candle_action296_certified_batch_axioms_before = axioms ();;
let candle_action296_certified_batch_size = 4;;

let candle_action296_certified_batch_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_certified_batch_collect remaining domain_th tree =
  if remaining = 0 then 0,[] else
  match tree with
  | P_result_pass (status,function_index,raw_flag) ->
      remaining - 1,[status,function_index,raw_flag,domain_th]
  | P_result_glue (_,split_index,convex_flag,left,right) ->
      if convex_flag then
        failwith "action296 certified batch: unexpected convex branch";
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      let after_left,left_leaves =
        candle_action296_certified_batch_collect
          remaining left_domain left in
      let after_right,right_leaves =
        candle_action296_certified_batch_collect
          after_left right_domain right in
      after_right,left_leaves @ right_leaves
  | P_result_mono _ ->
      failwith "action296 certified batch: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 certified batch: unexpected reference node";;

let candle_action296_certified_batch_remaining,
    candle_action296_certified_batch_leaves =
  candle_action296_certified_batch_collect
    candle_action296_certified_batch_size
    candle_action296_certified_batch_root_domain
    candle_action296_plan_precision_tree;;

if candle_action296_certified_batch_remaining <> 0 ||
   length candle_action296_certified_batch_leaves <>
     candle_action296_certified_batch_size ||
   not
     (List.for_all
       (fun (_,function_index,raw_flag,_) ->
         function_index = 0 && not raw_flag)
       candle_action296_certified_batch_leaves) then
  failwith "action296 certified batch: selected leaves drift";;

let candle_action296_certified_batch_profile_events : string list ref =
  ref [];;

let _ =
  candle_q_dim_analytic_jet_profile :=
    (fun event ->
      candle_action296_certified_batch_profile_events :=
        event :: !candle_action296_certified_batch_profile_events;
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_STAGE event=" ^ event));;

let candle_action296_certified_batch_attempts = ref 0;;
let candle_action296_certified_batch_accepted_cells = ref 0;;
let candle_action296_certified_batch_retries = ref 0;;
let candle_action296_certified_batch_max_depth = 12;;

let candle_action296_certified_batch_dest_cexp_num tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [value] -> dest_numeral value
    | _ -> failwith "action296 certified batch: malformed cexp number"
  else failwith "action296 certified batch: expected cexp number";;

let candle_action296_certified_batch_q_float value =
  let signed,denominator_predecessor =
    candle_q_dim_analytic_jet_dest_pair value in
  let positive_term,negative_term =
    candle_q_dim_analytic_jet_dest_pair signed in
  let positive =
    candle_action296_certified_batch_dest_cexp_num positive_term and
      negative =
        candle_action296_certified_batch_dest_cexp_num negative_term and
      denominator =
        Num.add_num
          (candle_action296_certified_batch_dest_cexp_num
            denominator_predecessor)
          (Num.num_of_int 1) in
  Num.float_of_num
    (Num.div_num (Num.sub_num positive negative) denominator);;

let rec candle_action296_certified_batch_dest_list value =
  let operator,arguments = strip_comb value in
  if aconv operator `Cexp_num` then []
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_action296_certified_batch_dest_list tail
    | _ -> failwith "action296 certified batch: malformed reflected list"
  else failwith "action296 certified batch: expected reflected list";;

let candle_action296_certified_batch_split_axis domain_th result =
  let _,after_domain =
    candle_q_dim_analytic_jet_dest_pair result in
  let _,after_center =
    candle_q_dim_analytic_jet_dest_pair after_domain in
  let _,after_value =
    candle_q_dim_analytic_jet_dest_pair after_center in
  let gradient_bounds,_ =
    candle_q_dim_analytic_jet_dest_pair after_value in
  let gradient_intervals =
    candle_action296_certified_batch_dest_list gradient_bounds in
  let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
  let actual_lower,actual_upper = dest_pair domain_pair in
  let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
      upper,_ = candle_reflected_nl_normalize_vector actual_upper in
  let widths =
    map2
      (fun lower_term upper_term ->
        Num.float_of_num
          (Num.abs_num
            (Num.sub_num
              (rat_of_term upper_term) (rat_of_term lower_term))))
      lower upper in
  if length widths <> 6 || length gradient_intervals <> 6 then
    failwith "action296 certified batch: split-score shape";
  let scores =
    map2
      (fun width interval ->
        let lower_gradient,upper_gradient =
          candle_q_dim_analytic_jet_dest_pair interval in
        let lower_magnitude =
          Float.abs
            (candle_action296_certified_batch_q_float lower_gradient) and
            upper_magnitude =
              Float.abs
                (candle_action296_certified_batch_q_float upper_gradient) in
        let magnitude =
          if Float.compare lower_magnitude upper_magnitude = 1 then
            lower_magnitude
          else upper_magnitude in
        width *. magnitude)
      widths gradient_intervals in
  let rec largest index best_index best_score remaining =
    match remaining with
    | [] -> best_index,best_score
    | score :: tail ->
        if Float.compare score best_score = 1 then
          largest (index + 1) index score tail
        else largest (index + 1) best_index best_score tail in
  largest 1 1 (~-. 1.0) scores;;

let candle_action296_certified_batch_prove_cell
    leaf_index depth box_prepared domain_th =
  let attempt = !candle_action296_certified_batch_attempts + 1 in
  candle_action296_certified_batch_attempts := attempt;
  print_endline
    ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_CELL leaf=" ^
     string_of_int leaf_index ^ " depth=" ^ string_of_int depth ^
     " attempt=" ^ string_of_int attempt ^ " event=begin");
  let theorem =
    candle_reflected_nl_source_pass_with
      candle_action296_plan_prepared.function_term
      (fun lower upper ->
        let center_variant =
          candle_q_dim_taylor_model_prepare_point_variant_six
            box_prepared lower upper in
        candle_q_dim_taylor_model_certified_prove_box_variant_six
          center_variant box_prepared
          lower upper)
      domain_th in
  candle_action296_certified_batch_accepted_cells :=
    !candle_action296_certified_batch_accepted_cells + 1;
  print_endline
    ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_CELL leaf=" ^
     string_of_int leaf_index ^ " depth=" ^ string_of_int depth ^
     " attempt=" ^ string_of_int attempt ^ " event=end");
  theorem;;

let rec candle_action296_certified_batch_adaptive
    leaf_index depth box_prepared domain_th =
  try
    candle_action296_certified_batch_prove_cell
      leaf_index depth box_prepared domain_th
  with Candle_q_dim_taylor_model_certified_rejected (result,upper) ->
    let program_domain,_ =
      candle_q_dim_analytic_jet_dest_pair result in
    if not (aconv program_domain `Cexp_num 1`) then
      (print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_FAILURE leaf=" ^
         string_of_int leaf_index ^ " depth=" ^ string_of_int depth ^
         " reason=domain upper=" ^ string_of_term upper);
       failwith "action296 certified batch: domain guard rejected")
    else if depth >= candle_action296_certified_batch_max_depth then
      (print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_FAILURE leaf=" ^
         string_of_int leaf_index ^ " depth=" ^ string_of_int depth ^
         " upper=" ^ string_of_term upper);
       failwith "action296 certified batch: subdivision limit")
    else
      let retry = !candle_action296_certified_batch_retries + 1 in
      let axis,score =
        candle_action296_certified_batch_split_axis domain_th result in
      candle_action296_certified_batch_retries := retry;
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_RETRY leaf=" ^
         string_of_int leaf_index ^ " depth=" ^ string_of_int depth ^
         " axis=" ^ string_of_int axis ^
         " score=" ^ string_of_float score ^
         " upper=" ^ string_of_term upper ^
         " retry=" ^ string_of_int retry);
      let left_domain,right_domain =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 axis domain_th in
      let left_theorem =
        candle_action296_certified_batch_adaptive
          leaf_index (depth + 1) box_prepared left_domain in
      let right_theorem =
        candle_action296_certified_batch_adaptive
          leaf_index (depth + 1) box_prepared right_domain in
      M_verifier.merge_m_cell_list_pass candle_action296_plan_dimension
        (M_verifier.m_glue_cells_list
          candle_action296_plan_dimension axis
          left_theorem right_theorem);;

let rec candle_action296_certified_batch_prove index leaves =
  match leaves with
  | [] -> []
  | (_,_,_,domain_th) :: tail ->
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_LEAF leaf=" ^
         string_of_int index ^ " event=begin");
      let domain_pair,_,_ = M_taylor.dest_m_cell_domain (concl domain_th) in
      let actual_lower,actual_upper = dest_pair domain_pair in
      let lower,_ = candle_reflected_nl_normalize_vector actual_lower and
          upper,_ = candle_reflected_nl_normalize_vector actual_upper in
      let box_prepared =
        candle_q_dim_analytic_jet_prepare_box_six
          candle_action296_plan_prepared.function_term lower upper in
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_LEAF leaf=" ^
         string_of_int index ^ " event=box-prepared");
      let theorem =
        candle_action296_certified_batch_adaptive
          index 0 box_prepared domain_th in
      let functions,proved_domain =
        M_verifier.dest_m_cell_list_pass (concl theorem) in
      let expected_domain,_,_ =
        M_taylor.dest_m_cell_domain (concl domain_th) in
      if functions <> [candle_action296_plan_prepared.function_term] ||
         not (aconv proved_domain expected_domain) ||
         hyp theorem <> [] then
        failwith "action296 certified batch: leaf theorem mismatch";
      print_endline
        ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_LEAF leaf=" ^
         string_of_int index ^ " event=end theorem_md5=" ^
         Digest.to_hex (Digest.string (string_of_thm theorem)));
      theorem ::
        candle_action296_certified_batch_prove (index + 1) tail;;

let candle_action296_certified_batch_theorems =
  candle_action296_certified_batch_prove 0
    candle_action296_certified_batch_leaves;;

let candle_action296_certified_batch_axioms_after = axioms ();;

if length candle_action296_certified_batch_theorems <>
     candle_action296_certified_batch_size ||
   length candle_action296_certified_batch_axioms_after <>
     length candle_action296_certified_batch_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_certified_batch_axioms_before)
       candle_action296_certified_batch_axioms_after) then
  failwith "action296 certified batch: final validation failed";;

print_endline
  ("CANDLE_CV_ACTION296_CERTIFIED_BATCH_RESULT leaves=" ^
   string_of_int (length candle_action296_certified_batch_theorems) ^
   " accepted_cells=" ^
   string_of_int !candle_action296_certified_batch_accepted_cells ^
   " attempts=" ^ string_of_int !candle_action296_certified_batch_attempts ^
   " retries=" ^ string_of_int !candle_action296_certified_batch_retries ^
   " profile_events=" ^
   string_of_int (length !candle_action296_certified_batch_profile_events));
print_endline "CANDLE_CV_ACTION296_CERTIFIED_BATCH_OK DEVELOPMENT_NON_RELEASE";;
