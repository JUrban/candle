(* ========================================================================== *)
(* Internally batched profile of genuine action-296 fixed-hybrid steps.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Untrusted preparation captures the authentic  *)
(* operands presented to every instruction for eight distinct accepted       *)
(* subboxes.  Polynomial, rational-algebraic, and nonlinear-composition steps *)
(* are evaluated in separate internal Kernel.compute batches.  A force-only   *)
(* batch returns one bit after checking only the outer result constructor; an  *)
(* exact batch also compares every result with its captured concrete value.    *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_action296_fixed_instruction_profile.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;

let candle_action296_aggregate_instruction_profile_axioms_before = axioms ();;

let candle_action296_aggregate_instruction_profile_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-aggregate-instruction-profile scope=" ^
     scope ^ " phase=" ^ phase ^ " event=" ^ event);;

(* An argument bundle is

     center_boxes, boxes, radii, center_instruction, box_instruction, stack.

   The final stack is deliberately the unpaired tail: the five preceding
   values are recovered with FST and successive SND projections. *)

let candle_cv_fs_q_dim_taylor_model_step_job_def = new_definition
 `candle_cv_fs_q_dim_taylor_model_step_job job =
    candle_cv_fs_q_dim_taylor_model_program_step
      (Cexp_fst job)
      (Cexp_fst (Cexp_snd job))
      (Cexp_fst (Cexp_snd (Cexp_snd job)))
      (Cexp_fst (Cexp_snd (Cexp_snd (Cexp_snd job))))
      (Cexp_fst
        (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd job)))))
      (Cexp_snd
        (Cexp_snd (Cexp_snd (Cexp_snd (Cexp_snd job)))))`;;

let candle_cv_fs_q_dim_taylor_model_step_force_batch_def = define
 `(candle_cv_fs_q_dim_taylor_model_step_force_batch (Cexp_num n) =
      Cexp_num 1) /\
  (candle_cv_fs_q_dim_taylor_model_step_force_batch
      (Cexp_pair job jobs) =
     Cexp_if
       (Cexp_ispair (candle_cv_fs_q_dim_taylor_model_step_job job))
       (candle_cv_fs_q_dim_taylor_model_step_force_batch jobs)
       (Cexp_num 0))`;;

let candle_cv_fs_q_dim_taylor_model_step_force_batch_compute = prove
 (`!jobs.
     candle_cv_fs_q_dim_taylor_model_step_force_batch jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (Cexp_ispair
           (candle_cv_fs_q_dim_taylor_model_step_job (Cexp_fst jobs)))
         (candle_cv_fs_q_dim_taylor_model_step_force_batch (Cexp_snd jobs))
         (Cexp_num 0))
       (Cexp_num 1)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_q_dim_taylor_model_step_force_batch_def;
              cexp_if_def; cexp_fst_def; cexp_snd_def;
              cexp_ispair_def]);;

(* Exact jobs pair the same argument bundle with the captured expected stack. *)

let candle_cv_fs_q_dim_taylor_model_step_exact_batch_def = define
 `(candle_cv_fs_q_dim_taylor_model_step_exact_batch (Cexp_num n) =
      Cexp_num 1) /\
  (candle_cv_fs_q_dim_taylor_model_step_exact_batch
      (Cexp_pair job jobs) =
     Cexp_if
       (Cexp_eq
         (candle_cv_fs_q_dim_taylor_model_step_job (Cexp_fst job))
         (Cexp_snd job))
       (candle_cv_fs_q_dim_taylor_model_step_exact_batch jobs)
       (Cexp_num 0))`;;

let candle_cv_fs_q_dim_taylor_model_step_exact_batch_compute = prove
 (`!jobs.
     candle_cv_fs_q_dim_taylor_model_step_exact_batch jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_if
         (Cexp_eq
           (candle_cv_fs_q_dim_taylor_model_step_job
             (Cexp_fst (Cexp_fst jobs)))
           (Cexp_snd (Cexp_fst jobs)))
         (candle_cv_fs_q_dim_taylor_model_step_exact_batch (Cexp_snd jobs))
         (Cexp_num 0))
       (Cexp_num 1)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_fs_q_dim_taylor_model_step_exact_batch_def;
              cexp_if_def; cexp_fst_def; cexp_snd_def;
              cexp_ispair_def]);;

let candle_action296_aggregate_instruction_profile_compute_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    (map SPEC_ALL
      [candle_cv_fs_q_dim_taylor_model_step_job_def;
       candle_cv_fs_q_dim_taylor_model_step_force_batch_compute;
       candle_cv_fs_q_dim_taylor_model_step_exact_batch_compute]);;

let candle_action296_aggregate_instruction_profile_compute tm =
  candle_q_dim_analytic_jet_compute
    candle_action296_aggregate_instruction_profile_compute_eqs tm;;

let candle_action296_aggregate_instruction_profile_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_action296_aggregate_instruction_profile_arguments
    center_boxes boxes radii center_instruction box_instruction stack =
  candle_action296_aggregate_instruction_profile_pair center_boxes
    (candle_action296_aggregate_instruction_profile_pair boxes
      (candle_action296_aggregate_instruction_profile_pair radii
        (candle_action296_aggregate_instruction_profile_pair
          center_instruction
          (candle_action296_aggregate_instruction_profile_pair
            box_instruction stack))));;

let rec candle_action296_aggregate_instruction_profile_list = function
  | [] -> `Cexp_num 0`
  | head :: tail ->
      candle_action296_aggregate_instruction_profile_pair head
        (candle_action296_aggregate_instruction_profile_list tail);;

let candle_action296_aggregate_instruction_profile_capture
    (variant,lower,upper) =
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
  let center_boxes_th =
    candle_action296_aggregate_instruction_profile_compute
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_term)) in
  let center_boxes = rand (concl center_boxes_th) in
  let radii_th =
    candle_action296_aggregate_instruction_profile_compute
      (mk_comb
        (`candle_cv_q_fixed_list_round_upper`,
         mk_comb (`candle_cv_q_radius_list`,boxes_term))) in
  let radii = rand (concl radii_th) in
  let rec capture center_remaining box_remaining value_stack =
    match center_remaining,box_remaining with
    | [],[] -> [],[],[]
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
                   "action296 aggregate instruction profile: unary underflow")
          else
            (match value_stack with
             | right :: left :: remaining -> [right;left],remaining
             | _ ->
                 failwith
                   "action296 aggregate instruction profile: binary underflow") in
        let reflected_operand_stack =
          candle_action296_instruction_profile_term_stack operand_stack in
        let arguments =
          candle_action296_aggregate_instruction_profile_arguments
            center_boxes boxes_term radii center_instruction box_instruction
            reflected_operand_stack in
        let step_th =
          candle_action296_aggregate_instruction_profile_compute
            (mk_comb
              (`candle_cv_fs_q_dim_taylor_model_step_job`,arguments)) in
        let expected_stack = rand (concl step_th) in
        let result =
          candle_action296_instruction_profile_top expected_stack in
        let polynomial_tail,algebraic_tail,nonlinear_tail =
          capture center_tail box_tail (result :: remaining_stack) in
        let job = arguments,expected_stack in
        if opcode = "poly" then
          job :: polynomial_tail,algebraic_tail,nonlinear_tail
        else if opcode = "add" || opcode = "mul" then
          polynomial_tail,job :: algebraic_tail,nonlinear_tail
        else
          polynomial_tail,algebraic_tail,job :: nonlinear_tail
    | _ ->
        failwith "action296 aggregate instruction profile: program mismatch" in
  capture center_instructions box_instructions [];;

let candle_action296_aggregate_instruction_profile_force_jobs jobs =
  candle_action296_aggregate_instruction_profile_list (map fst jobs);;

let candle_action296_aggregate_instruction_profile_exact_jobs jobs =
  candle_action296_aggregate_instruction_profile_list
    (map
      (fun (arguments,expected) ->
        candle_action296_aggregate_instruction_profile_pair
          arguments expected)
      jobs);;

let candle_action296_aggregate_instruction_profile_expect_one label th =
  if not (aconv (rand (concl th)) `Cexp_num 1`) then
    failwith
      ("action296 aggregate instruction profile: " ^ label ^ " failed");;

let candle_action296_aggregate_instruction_profile_run
    scope jobs expected_count =
  if length jobs <> expected_count then
    failwith
      ("action296 aggregate instruction profile: " ^ scope ^
       " cardinality drift");
  let force_input =
    candle_action296_aggregate_instruction_profile_force_jobs jobs and
      exact_input =
        candle_action296_aggregate_instruction_profile_exact_jobs jobs in
  let run_force phase =
    candle_action296_aggregate_instruction_profile_marker
      scope phase "begin";
    let theorem =
      candle_action296_aggregate_instruction_profile_compute
        (mk_comb
          (`candle_cv_fs_q_dim_taylor_model_step_force_batch`,force_input)) in
    candle_action296_aggregate_instruction_profile_marker scope phase "end";
    candle_action296_aggregate_instruction_profile_expect_one
      (scope ^ " " ^ phase) theorem in
  run_force "force-pass-1";
  run_force "force-pass-2";
  candle_action296_aggregate_instruction_profile_marker
    scope "exact-pass" "begin";
  let exact_theorem =
    candle_action296_aggregate_instruction_profile_compute
      (mk_comb
        (`candle_cv_fs_q_dim_taylor_model_step_exact_batch`,exact_input)) in
  candle_action296_aggregate_instruction_profile_marker
    scope "exact-pass" "end";
  candle_action296_aggregate_instruction_profile_expect_one
    (scope ^ " exact-pass") exact_theorem;
  print_endline
    ("CANDLE_CV_ACTION296_AGGREGATE_INSTRUCTION_PARTITION_PASS partition=" ^
     scope ^ " jobs=" ^ string_of_int expected_count ^
     " force_passes=2 exact_passes=1");;

let rec candle_action296_aggregate_instruction_profile_run_chunks
    chunk_index cases =
  match cases with
  | first :: remaining ->
      let chunk = "chunk-" ^ string_of_int chunk_index in
      candle_action296_aggregate_instruction_profile_marker
        chunk "authentic-step-capture" "begin";
      let first_polynomial,first_algebraic,first_nonlinear =
        candle_action296_aggregate_instruction_profile_capture first in
      candle_action296_aggregate_instruction_profile_marker
        chunk "authentic-step-capture" "end";
      candle_action296_aggregate_instruction_profile_run
        ("polynomial-" ^ chunk) first_polynomial 22;
      candle_action296_aggregate_instruction_profile_run
        ("algebraic-" ^ chunk) first_algebraic 22;
      candle_action296_aggregate_instruction_profile_run
        ("nonlinear-" ^ chunk) first_nonlinear 10;
      candle_action296_aggregate_instruction_profile_run_chunks
        (chunk_index + 1) remaining
  | [] -> ()
;;

let _ =
  candle_action296_aggregate_instruction_profile_marker
    "batch" "profiled-run" "begin";;

let _ =
  candle_action296_aggregate_instruction_profile_run_chunks 1
    candle_action296_instruction_profile_cases;;

let candle_action296_aggregate_instruction_profile_axioms_after = axioms ();;

if length candle_action296_aggregate_instruction_profile_axioms_after <>
     length candle_action296_aggregate_instruction_profile_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem
           candle_action296_aggregate_instruction_profile_axioms_before)
       candle_action296_aggregate_instruction_profile_axioms_after) then
  failwith "action296 aggregate instruction profile: axiom drift";;

let _ =
  candle_action296_aggregate_instruction_profile_marker
    "batch" "profiled-run" "end";;

print_endline
  "CANDLE_CV_ACTION296_AGGREGATE_INSTRUCTION_PROFILE_RESULT boxes=8 polynomial_jobs=176 algebraic_jobs=176 nonlinear_jobs=80 force_passes=2 exact_passes=1";;
print_endline
  "CANDLE_CV_ACTION296_AGGREGATE_INSTRUCTION_PROFILE_OK DEVELOPMENT_NON_RELEASE";;
