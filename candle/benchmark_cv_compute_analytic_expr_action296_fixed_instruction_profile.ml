(* ========================================================================== *)
(* Per-instruction profile of the proved genuine action-296 fixed hybrid.     *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This reuses the eight accepted genuine boxes  *)
(* and exact source preparations from the rational instruction profile.  Each *)
(* fixed-hybrid program is executed one checked step at a time and compared   *)
(* with its fixed-hybrid one-shot result.                                      *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_instruction_profile.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_compute.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

let candle_action296_fixed_instruction_profile_axioms_before = axioms ();;

let candle_action296_fixed_instruction_profile_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-instruction-profile scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

let candle_action296_fixed_instruction_profile_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_cv_fs_q_dim_taylor_model_compute_eqs tm;;

let rec candle_action296_fixed_instruction_profile_control count =
  if count <= 0 then ()
  else
    let _ =
      candle_action296_fixed_instruction_profile_compute `Cexp_num 0` in
    candle_action296_fixed_instruction_profile_control (count - 1);;

let _ =
  candle_action296_fixed_instruction_profile_marker
    "batch" "profiled-run" "begin";;
let _ =
  candle_action296_fixed_instruction_profile_marker
    "control" "432-value-computes" "begin";;
let _ = candle_action296_fixed_instruction_profile_control (8 * 54);;
let _ =
  candle_action296_fixed_instruction_profile_marker
    "control" "432-value-computes" "end";;

let candle_action296_fixed_instruction_profile_run
    box_index (variant,lower,upper) =
  let scope = "box-" ^ string_of_int box_index in
  candle_action296_fixed_instruction_profile_marker
    scope "input-encoding" "begin";
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
  candle_action296_fixed_instruction_profile_marker
    scope "input-encoding" "end";
  if length center_instructions <> 54 || length box_instructions <> 54 then
    failwith "action296 fixed instruction profile: instruction drift";
  candle_action296_fixed_instruction_profile_marker
    scope "box-setup" "begin";
  let center_boxes_th =
    candle_action296_fixed_instruction_profile_compute
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_term)) in
  let center_boxes = rand (concl center_boxes_th) in
  let radii_th =
    candle_action296_fixed_instruction_profile_compute
      (mk_comb
        (`candle_cv_q_fixed_list_round_upper`,
         mk_comb (`candle_cv_q_radius_list`,boxes_term))) in
  let radii = rand (concl radii_th) in
  candle_action296_fixed_instruction_profile_marker scope "box-setup" "end";
  let rec run_steps index center_remaining box_remaining value_stack =
    match center_remaining,box_remaining with
    | [],[] -> value_stack
    | center_instruction :: center_tail,
      box_instruction :: box_tail ->
        let opcode,_ =
          candle_action296_instruction_profile_opcode center_instruction in
        let arity = candle_action296_instruction_profile_arity opcode in
        let operand_stack,remaining_stack =
          if arity = 0 then [],value_stack
          else if arity = 1 then
            (match value_stack with
             | value :: remaining -> [value],remaining
             | [] ->
                 failwith
                   "action296 fixed instruction profile: unary underflow")
          else
            (match value_stack with
             | right :: left :: remaining -> [right;left],remaining
             | _ ->
                 failwith
                   "action296 fixed instruction profile: binary underflow") in
        let reflected_operand_stack =
          candle_action296_instruction_profile_term_stack operand_stack in
        let phase =
          "instruction-" ^
          candle_action296_instruction_profile_pad index ^ "-" ^ opcode in
        candle_action296_fixed_instruction_profile_marker
          scope phase "begin";
        let step_th =
          candle_action296_fixed_instruction_profile_compute
            (list_mk_comb
              (`candle_cv_fs_q_dim_taylor_model_program_step`,
               [center_boxes;boxes_term;radii;
                center_instruction;box_instruction;
                reflected_operand_stack])) in
        let next_reflected_stack = rand (concl step_th) in
        let result =
          candle_action296_instruction_profile_top next_reflected_stack in
        candle_action296_fixed_instruction_profile_marker scope phase "end";
        run_steps (index + 1) center_tail box_tail
          (result :: remaining_stack)
    | _ ->
        failwith "action296 fixed instruction profile: program mismatch" in
  candle_action296_fixed_instruction_profile_marker
    scope "stepwise-total" "begin";
  let final_stack =
    run_steps 0 center_instructions box_instructions [] in
  let stepwise_result =
    match final_stack with
    | [result] -> result
    | _ ->
        failwith "action296 fixed instruction profile: final stack shape" in
  candle_action296_fixed_instruction_profile_marker
    scope "stepwise-total" "end";
  candle_action296_fixed_instruction_profile_marker scope "one-shot" "begin";
  let one_shot_th =
    candle_action296_fixed_instruction_profile_compute
      (list_mk_comb
        (`candle_cv_fs_q_dim_taylor_model_program`,
         [center_program;box_program;boxes_term])) in
  let one_shot_result = rand (concl one_shot_th) in
  candle_action296_fixed_instruction_profile_marker scope "one-shot" "end";
  if not (aconv stepwise_result one_shot_result) then
    failwith "action296 fixed instruction profile: one-shot mismatch";
  let finish_th =
    candle_action296_fixed_instruction_profile_compute
      (list_mk_comb
        (`candle_cv_q_dim_taylor_model_certified_finish`,
         [boxes_term;stepwise_result])) in
  let flag,_ =
    candle_q_dim_analytic_jet_dest_pair (rand (concl finish_th)) in
  if not (aconv flag `Cexp_num 1`) then
    failwith "action296 fixed instruction profile: accepted box rejected";
  print_endline
    ("CANDLE_CV_ACTION296_FIXED_INSTRUCTION_BOX_PASS box=" ^
     string_of_int box_index ^ " instructions=54 exact_one_shot=1");;

let rec candle_action296_fixed_instruction_profile_run_all index = function
  | [] -> ()
  | case :: remaining ->
      candle_action296_fixed_instruction_profile_run index case;
      candle_action296_fixed_instruction_profile_run_all
        (index + 1) remaining;;

let _ =
  candle_action296_fixed_instruction_profile_run_all 1
    candle_action296_instruction_profile_cases;;

let candle_action296_fixed_instruction_profile_axioms_after = axioms ();;

if length candle_action296_instruction_profile_cases <> 8 ||
   length candle_action296_fixed_instruction_profile_axioms_after <>
     length candle_action296_fixed_instruction_profile_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_fixed_instruction_profile_axioms_before)
       candle_action296_fixed_instruction_profile_axioms_after) then
  failwith "action296 fixed instruction profile: final validation failed";;

let _ =
  candle_action296_fixed_instruction_profile_marker
    "batch" "profiled-run" "end";;

print_endline
  "CANDLE_CV_ACTION296_FIXED_INSTRUCTION_PROFILE_RESULT boxes=8 instructions=432 exact_one_shot=8 accepted=8";;
print_endline
  "CANDLE_CV_ACTION296_FIXED_INSTRUCTION_PROFILE_OK DEVELOPMENT_NON_RELEASE";;
