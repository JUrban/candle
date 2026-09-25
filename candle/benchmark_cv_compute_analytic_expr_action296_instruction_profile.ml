(* ========================================================================== *)
(* Per-instruction profile of the genuine action-296 centered Taylor model.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Eight distinct exact subboxes reuse one       *)
(* authenticated whole-box source.  Each 54-instruction program is executed *)
(* one checked step at a time, carrying the exact concrete stack forward.    *)
(* External markers time every step.  Untrusted ML scans of the resulting    *)
(* concrete cvals report rational/numeral sizes; they authorize no theorem.  *)
(* A one-shot execution must reproduce each final stepwise result exactly.   *)
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
open Candle_cv_analytic_expr_taylor_model_program_compute;;
open Candle_cv_analytic_expr_taylor_model_certified_compute;;

let candle_action296_instruction_profile_axioms_before = axioms ();;

let candle_action296_instruction_profile_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-instruction-profile scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

let _ =
  candle_action296_instruction_profile_marker
    "batch" "profiled-run" "begin";;

let candle_action296_instruction_profile_root_domain =
  M_taylor.mk_m_center_domain
    candle_action296_plan_dimension 6
    candle_action296_plan_xx1 candle_action296_plan_zz1;;

let rec candle_action296_instruction_profile_find domain_th tree =
  match tree with
  | P_result_pass (_,function_index,raw_flag) ->
      if function_index <> 0 || raw_flag then
        failwith "action296 instruction profile: unexpected pass selection";
      domain_th
  | P_result_glue (_,split_index,convex_flag,left,_) ->
      if convex_flag then
        failwith "action296 instruction profile: unexpected convex branch";
      let left_domain,_ =
        M_verifier.split_domain
          candle_action296_plan_dimension 6 (split_index + 1) domain_th in
      candle_action296_instruction_profile_find left_domain left
  | P_result_mono _ ->
      failwith "action296 instruction profile: unexpected monotonicity node"
  | P_result_ref _ ->
      failwith "action296 instruction profile: unexpected reference node";;

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

let _ =
  candle_action296_instruction_profile_marker
    "shared" "whole-box-source-preparation" "begin";;
let candle_action296_instruction_profile_box_prepared =
  candle_q_dim_analytic_jet_prepare_box_six
    candle_action296_plan_prepared.function_term
    candle_action296_instruction_profile_probe_lower
    candle_action296_instruction_profile_probe_upper;;
let _ =
  candle_action296_instruction_profile_marker
    "shared" "whole-box-source-preparation" "end";;

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

let _ =
  candle_action296_instruction_profile_marker
    "shared" "center-variant-preparation" "begin";;
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
    "shared" "center-variant-preparation" "end";;

type candle_action296_instruction_profile_cval =
  | Candle_action296_instruction_num of num
  | Candle_action296_instruction_pair of term * term;;

let candle_action296_instruction_profile_view tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then
    match arguments with
    | [argument] ->
        Candle_action296_instruction_num (dest_numeral argument)
    | _ -> failwith "action296 instruction profile: malformed Cexp_num"
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> Candle_action296_instruction_pair (left,right)
    | _ -> failwith "action296 instruction profile: malformed Cexp_pair"
  else failwith "action296 instruction profile: non-concrete cval";;

let rec candle_action296_instruction_profile_list tm =
  match candle_action296_instruction_profile_view tm with
  | Candle_action296_instruction_num n ->
      if Num.eq_num n (Num.num_of_int 0) then []
      else failwith "action296 instruction profile: malformed cval list tail"
  | Candle_action296_instruction_pair (head,tail) ->
      head :: candle_action296_instruction_profile_list tail;;

let candle_action296_instruction_profile_top stack =
  match candle_action296_instruction_profile_view stack with
  | Candle_action296_instruction_pair (head,_) -> head
  | Candle_action296_instruction_num _ ->
      failwith "action296 instruction profile: empty result stack";;

let candle_action296_instruction_profile_num_bits n =
  let zero = Num.num_of_int 0 and two = Num.num_of_int 2 in
  let rec loop value bits =
    if Num.eq_num value zero then bits
    else loop (Num.quo_num value two) (bits + 1) in
  loop n 0;;

type candle_action296_instruction_profile_stats = {
  instruction_numerals: int;
  instruction_rationals: int;
  instruction_scale_denominators: int;
  instruction_max_raw_bits: int;
  instruction_max_numerator_bits: int;
  instruction_max_denominator_bits: int
};;

let candle_action296_instruction_profile_stats tm =
  let numeral_count = ref 0 and rational_count = ref 0 and
      scale_denominators = ref 0 and
      max_raw = ref (Num.num_of_int 0) and
      max_numerator = ref (Num.num_of_int 0) and
      max_denominator = ref (Num.num_of_int 0) in
  let record_raw value =
    numeral_count := !numeral_count + 1;
    if Num.gt_num value !max_raw then max_raw := value in
  let record_rational positive negative denominator_predecessor =
    rational_count := !rational_count + 1;
    record_raw positive;
    record_raw negative;
    record_raw denominator_predecessor;
    let numerator = Num.add_num positive negative and
        denominator =
          Num.add_num denominator_predecessor (Num.num_of_int 1) in
    if Num.gt_num numerator !max_numerator then
      max_numerator := numerator;
    if Num.gt_num denominator !max_denominator then
      max_denominator := denominator;
    if Num.string_of_num denominator = "1000000000000" then
      scale_denominators := !scale_denominators + 1 in
  let rec scan value =
    match candle_action296_instruction_profile_view value with
    | Candle_action296_instruction_num n -> record_raw n
    | Candle_action296_instruction_pair (left,right) ->
        (match candle_action296_instruction_profile_view left,
               candle_action296_instruction_profile_view right with
         | Candle_action296_instruction_pair (positive_tm,negative_tm),
           Candle_action296_instruction_num denominator_predecessor ->
             (match candle_action296_instruction_profile_view positive_tm,
                    candle_action296_instruction_profile_view negative_tm with
              | Candle_action296_instruction_num positive,
                Candle_action296_instruction_num negative ->
                  record_rational
                    positive negative denominator_predecessor
              | _ -> scan left; scan right)
         | _ -> scan left; scan right) in
  scan tm;
  {instruction_numerals = !numeral_count;
   instruction_rationals = !rational_count;
   instruction_scale_denominators = !scale_denominators;
   instruction_max_raw_bits =
     candle_action296_instruction_profile_num_bits !max_raw;
   instruction_max_numerator_bits =
     candle_action296_instruction_profile_num_bits !max_numerator;
   instruction_max_denominator_bits =
     candle_action296_instruction_profile_num_bits !max_denominator};;

let candle_action296_instruction_profile_opcode instruction =
  match candle_action296_instruction_profile_view instruction with
  | Candle_action296_instruction_pair (tag,payload) ->
      (match candle_action296_instruction_profile_view tag with
       | Candle_action296_instruction_num n ->
           if Num.eq_num n (Num.num_of_int 0) then
             "poly",
             length (candle_action296_instruction_profile_list payload)
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

let candle_action296_instruction_profile_pad index =
  if index < 10 then "0" ^ string_of_int index else string_of_int index;;

let candle_action296_instruction_profile_arity opcode =
  if opcode = "poly" || opcode = "pi-half" then 0
  else if opcode = "neg" || opcode = "square" || opcode = "inv" ||
          opcode = "sqrt" || opcode = "atn" then 1
  else if opcode = "add" || opcode = "mul" then 2
  else failwith "action296 instruction profile: unknown opcode arity";;

let rec candle_action296_instruction_profile_term_stack = function
  | [] -> `Cexp_num 0`
  | head :: tail ->
      list_mk_comb
        (`Cexp_pair`,
         [head;candle_action296_instruction_profile_term_stack tail]);;

let candle_action296_instruction_profile_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_q_dim_taylor_model_certified_compute_eqs tm;;

let rec candle_action296_instruction_profile_control count =
  if count <= 0 then ()
  else
    let _ = candle_action296_instruction_profile_compute `Cexp_num 0` in
    candle_action296_instruction_profile_control (count - 1);;

let _ =
  candle_action296_instruction_profile_marker
    "control" "432-value-computes" "begin";;
let _ = candle_action296_instruction_profile_control (8 * 54);;
let _ =
  candle_action296_instruction_profile_marker
    "control" "432-value-computes" "end";;

let candle_action296_instruction_profile_run box_index (variant,lower,upper) =
  let scope = "box-" ^ string_of_int box_index in
  candle_action296_instruction_profile_marker scope "input-encoding" "begin";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  let boxes_term = rand (concl boxes_representation) in
  let center_program = variant.variant_program_representation_term and
      box_program =
        candle_action296_instruction_profile_box_prepared.
          program_representation_term in
  let center_instructions =
    candle_action296_instruction_profile_list center_program and
      box_instructions =
        candle_action296_instruction_profile_list box_program in
  candle_action296_instruction_profile_marker scope "input-encoding" "end";
  if length center_instructions <> 54 || length box_instructions <> 54 then
    failwith "action296 instruction profile: instruction cardinality drift";
  candle_action296_instruction_profile_marker scope "box-setup" "begin";
  let center_boxes_th =
    candle_action296_instruction_profile_compute
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_term)) in
  let center_boxes = rand (concl center_boxes_th) in
  let radii_th =
    candle_action296_instruction_profile_compute
      (mk_comb
        (`candle_cv_q_fixed_list_round_upper`,
         mk_comb (`candle_cv_q_radius_list`,boxes_term))) in
  let radii = rand (concl radii_th) in
  candle_action296_instruction_profile_marker scope "box-setup" "end";
  let rec run_steps index center_remaining box_remaining value_stack =
    match center_remaining,box_remaining with
    | [],[] -> value_stack
    | center_instruction :: center_tail,
      box_instruction :: box_tail ->
        let opcode,poly_instructions =
          candle_action296_instruction_profile_opcode center_instruction in
        let arity = candle_action296_instruction_profile_arity opcode in
        let operand_stack,remaining_stack =
          if arity = 0 then [],value_stack
          else if arity = 1 then
            (match value_stack with
             | value :: remaining -> [value],remaining
             | [] ->
                 failwith "action296 instruction profile: unary stack underflow")
          else
            (match value_stack with
             | right :: left :: remaining -> [right;left],remaining
             | _ ->
                 failwith "action296 instruction profile: binary stack underflow") in
        let reflected_operand_stack =
          candle_action296_instruction_profile_term_stack operand_stack in
        let phase =
          "instruction-" ^
          candle_action296_instruction_profile_pad index ^ "-" ^ opcode in
        candle_action296_instruction_profile_marker scope phase "begin";
        let step_th =
          candle_action296_instruction_profile_compute
            (list_mk_comb
              (`candle_cv_q_dim_taylor_model_program_step`,
               [center_boxes;boxes_term;radii;
                center_instruction;box_instruction;
                reflected_operand_stack])) in
        let next_reflected_stack = rand (concl step_th) in
        let result =
          candle_action296_instruction_profile_top next_reflected_stack in
        candle_action296_instruction_profile_marker scope phase "end";
        let stats =
          candle_action296_instruction_profile_stats result in
        print_endline
          ("CANDLE_CV_ACTION296_INSTRUCTION_STAT box=" ^
           string_of_int box_index ^
           " index=" ^ string_of_int index ^
           " opcode=" ^ opcode ^
           " poly_instructions=" ^ string_of_int poly_instructions ^
           " rationals=" ^ string_of_int stats.instruction_rationals ^
           " numerals=" ^ string_of_int stats.instruction_numerals ^
           " scale_denominators=" ^
             string_of_int stats.instruction_scale_denominators ^
           " max_raw_bits=" ^
             string_of_int stats.instruction_max_raw_bits ^
           " max_numerator_bits=" ^
             string_of_int stats.instruction_max_numerator_bits ^
           " max_denominator_bits=" ^
             string_of_int stats.instruction_max_denominator_bits);
        run_steps (index + 1) center_tail box_tail
          (result :: remaining_stack)
    | _ -> failwith "action296 instruction profile: program length mismatch" in
  candle_action296_instruction_profile_marker scope "stepwise-total" "begin";
  let final_stack =
    run_steps 0 center_instructions box_instructions [] in
  let stepwise_result =
    match final_stack with
    | [result] -> result
    | _ -> failwith "action296 instruction profile: non-singleton final stack" in
  candle_action296_instruction_profile_marker scope "stepwise-total" "end";
  candle_action296_instruction_profile_marker scope "one-shot" "begin";
  let one_shot_th =
    candle_action296_instruction_profile_compute
      (list_mk_comb
        (`candle_cv_q_dim_taylor_model_program`,
         [center_program;box_program;boxes_term])) in
  let one_shot_result = rand (concl one_shot_th) in
  candle_action296_instruction_profile_marker scope "one-shot" "end";
  if not (aconv stepwise_result one_shot_result) then
    failwith "action296 instruction profile: stepwise/one-shot mismatch";
  let finish_th =
    candle_action296_instruction_profile_compute
      (list_mk_comb
        (`candle_cv_q_dim_taylor_model_certified_finish`,
         [boxes_term;stepwise_result])) in
  let flag,_ =
    candle_q_dim_analytic_jet_dest_pair (rand (concl finish_th)) in
  if not (aconv flag `Cexp_num 1`) then
    failwith "action296 instruction profile: accepted box rejected";
  print_endline
    ("CANDLE_CV_ACTION296_INSTRUCTION_BOX_PASS box=" ^
     string_of_int box_index ^ " instructions=54 exact_one_shot=1");;

let rec candle_action296_instruction_profile_run_all index = function
  | [] -> ()
  | case :: remaining ->
      candle_action296_instruction_profile_run index case;
      candle_action296_instruction_profile_run_all (index + 1) remaining;;

let _ =
  candle_action296_instruction_profile_run_all 1
    candle_action296_instruction_profile_cases;;

let candle_action296_instruction_profile_axioms_after = axioms ();;

if length candle_action296_instruction_profile_cases <> 8 ||
   length candle_action296_instruction_profile_axioms_after <>
     length candle_action296_instruction_profile_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_instruction_profile_axioms_before)
       candle_action296_instruction_profile_axioms_after) then
  failwith "action296 instruction profile: final validation failed";;

let _ =
  candle_action296_instruction_profile_marker
    "batch" "profiled-run" "end";;

print_endline
  "CANDLE_CV_ACTION296_INSTRUCTION_PROFILE_RESULT boxes=8 instructions=432 exact_one_shot=8 accepted=8";;
print_endline
  "CANDLE_CV_ACTION296_INSTRUCTION_PROFILE_OK DEVELOPMENT_NON_RELEASE";;
