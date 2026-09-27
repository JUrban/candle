(* ========================================================================== *)
(* Genuine action-296 discriminator for fixed outer algebraic composition.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Eight accepted exact boxes share one source    *)
(* preparation.  The proved polynomial-only hybrid and the experimental       *)
(* tagged mixed-stack evaluator each return one aggregate acceptance count.    *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_benchmark_fixture.ml";;
needs "candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compute.ml";;

open Candle_cv_analytic_expr_taylor_model_program_fixed_compute;;
open Candle_cv_analytic_expr_taylor_model_program_fixed_algebraic_compute;;

let candle_action296_fixed_algebraic_axioms_before = axioms ();;

let candle_action296_fixed_algebraic_marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=action296-fixed-algebraic scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

let candle_cv_action296_fixed_algebraic_old_batch_def = define
 `(candle_cv_action296_fixed_algebraic_old_batch
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_fixed_algebraic_old_batch
      box_program (Cexp_pair job jobs) =
     Cexp_add
       (Cexp_fst
         (candle_cv_fs_q_dim_taylor_model_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_fixed_algebraic_old_batch
         box_program jobs))`;;

let candle_cv_action296_fixed_algebraic_old_batch_compute = prove
 (`!box_program jobs.
     candle_cv_action296_fixed_algebraic_old_batch box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_add
         (Cexp_fst
           (candle_cv_fs_q_dim_taylor_model_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_fixed_algebraic_old_batch
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_fixed_algebraic_old_batch_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_action296_fixed_algebraic_new_batch_def = define
 `(candle_cv_action296_fixed_algebraic_new_batch
      box_program (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_action296_fixed_algebraic_new_batch
      box_program (Cexp_pair job jobs) =
     Cexp_add
       (Cexp_fst
         (candle_cv_fsa_certified_check
           (Cexp_fst job) box_program (Cexp_snd job)))
       (candle_cv_action296_fixed_algebraic_new_batch
         box_program jobs))`;;

let candle_cv_action296_fixed_algebraic_new_batch_compute = prove
 (`!box_program jobs.
     candle_cv_action296_fixed_algebraic_new_batch box_program jobs =
     Cexp_if (Cexp_ispair jobs)
       (Cexp_add
         (Cexp_fst
           (candle_cv_fsa_certified_check
             (Cexp_fst (Cexp_fst jobs)) box_program
             (Cexp_snd (Cexp_fst jobs))))
         (candle_cv_action296_fixed_algebraic_new_batch
           box_program (Cexp_snd jobs)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `jobs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_action296_fixed_algebraic_new_batch_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_action296_fixed_algebraic_old_eqs =
  union candle_cv_fs_q_dim_taylor_model_compute_eqs
    [SPEC_ALL candle_cv_action296_fixed_algebraic_old_batch_compute];;

let candle_action296_fixed_algebraic_new_eqs =
  union candle_cv_fsa_compute_eqs
    [SPEC_ALL candle_cv_action296_fixed_algebraic_new_batch_compute];;

let candle_action296_fixed_algebraic_compute equations tm =
  candle_q_dim_analytic_jet_compute equations tm;;

let candle_action296_fixed_algebraic_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_action296_fixed_algebraic_job (variant,lower,upper) =
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv boxes in
  candle_action296_fixed_algebraic_pair
    variant.variant_program_representation_term
    (rand (concl boxes_representation));;

let candle_action296_fixed_algebraic_jobs =
  itlist
    (fun case tail ->
      candle_action296_fixed_algebraic_pair
        (candle_action296_fixed_algebraic_job case) tail)
    candle_action296_instruction_profile_cases `Cexp_num 0`;;

let candle_action296_fixed_algebraic_box_program =
  candle_action296_instruction_profile_box_prepared.
    program_representation_term;;

let _ =
  candle_action296_fixed_algebraic_marker
    "batch" "profiled-run" "begin";;

let _ =
  candle_action296_fixed_algebraic_marker
    "boxes-8" "polynomial-only-hybrid" "begin";;
let candle_action296_fixed_algebraic_old_result =
  candle_action296_fixed_algebraic_compute
    candle_action296_fixed_algebraic_old_eqs
    (list_mk_comb
      (`candle_cv_action296_fixed_algebraic_old_batch`,
       [candle_action296_fixed_algebraic_box_program;
        candle_action296_fixed_algebraic_jobs]));;
let _ =
  candle_action296_fixed_algebraic_marker
    "boxes-8" "polynomial-only-hybrid" "end";;

let _ =
  candle_action296_fixed_algebraic_marker
    "boxes-8" "fixed-algebraic-hybrid" "begin";;
let candle_action296_fixed_algebraic_new_result =
  candle_action296_fixed_algebraic_compute
    candle_action296_fixed_algebraic_new_eqs
    (list_mk_comb
      (`candle_cv_action296_fixed_algebraic_new_batch`,
       [candle_action296_fixed_algebraic_box_program;
        candle_action296_fixed_algebraic_jobs]));;
let _ =
  candle_action296_fixed_algebraic_marker
    "boxes-8" "fixed-algebraic-hybrid" "end";;

let candle_action296_fixed_algebraic_old_count =
  rand (concl candle_action296_fixed_algebraic_old_result) and
    candle_action296_fixed_algebraic_new_count =
      rand (concl candle_action296_fixed_algebraic_new_result);;

let candle_action296_fixed_algebraic_result_summary equations program case =
  let _,_,boxes =
    let variant,lower,upper = case in
    let encoded =
      candle_q_dim_analytic_jet_boxes_encode_conv
        (candle_poly_fixture_q_boxes lower upper) in
    variant,lower,rand (concl encoded) in
  let variant,_,_ = case in
  let result_theorem =
    candle_action296_fixed_algebraic_compute equations
      (list_mk_comb
        (program,
         [variant.variant_program_representation_term;
          candle_action296_fixed_algebraic_box_program;boxes])) in
  let result = rand (concl result_theorem) in
  let domain,result_tail = candle_q_dim_analytic_jet_dest_pair result in
  let _,cache_tail = candle_q_dim_analytic_jet_dest_pair result_tail in
  let value_bound,_ = candle_q_dim_analytic_jet_dest_pair cache_tail in
  let _,upper = candle_q_dim_analytic_jet_dest_pair value_bound in
  domain,upper;;

let candle_action296_fixed_algebraic_item_tag_domain item =
  match candle_action296_instruction_profile_view item with
  | Candle_action296_instruction_pair (tag,payload) ->
      (match candle_action296_instruction_profile_view tag,
             candle_action296_instruction_profile_view payload with
       | Candle_action296_instruction_num tag_number,
         Candle_action296_instruction_pair (domain,_) ->
           tag_number,domain
       | _ ->
           failwith
             "action296 fixed algebraic: malformed tagged result payload")
  | Candle_action296_instruction_num _ ->
      failwith "action296 fixed algebraic: malformed tagged result";;

let candle_action296_fixed_algebraic_item_payload item =
  match candle_action296_instruction_profile_view item with
  | Candle_action296_instruction_pair (_,payload) -> payload
  | Candle_action296_instruction_num _ ->
      failwith "action296 fixed algebraic: malformed tagged result";;

let candle_action296_fixed_algebraic_domain_upper result =
  let domain,result_tail = candle_q_dim_analytic_jet_dest_pair result in
  let _,cache_tail = candle_q_dim_analytic_jet_dest_pair result_tail in
  let value_bound,_ = candle_q_dim_analytic_jet_dest_pair cache_tail in
  let _,upper = candle_q_dim_analytic_jet_dest_pair value_bound in
  domain,upper;;

let candle_action296_fixed_algebraic_first_domain_loss
      (variant,lower,upper) =
  let boxes_representation =
    candle_q_dim_analytic_jet_boxes_encode_conv
      (candle_poly_fixture_q_boxes lower upper) in
  let boxes = rand (concl boxes_representation) in
  let center_boxes =
    rand
      (concl
        (candle_action296_fixed_algebraic_compute
          candle_action296_fixed_algebraic_new_eqs
          (mk_comb (`candle_cv_q_center_environment_list`,boxes)))) in
  let radii =
    rand
      (concl
        (candle_action296_fixed_algebraic_compute
          candle_action296_fixed_algebraic_new_eqs
          (mk_comb
            (`candle_cv_q_fixed_list_round_upper`,
             mk_comb (`candle_cv_q_radius_list`,boxes))))) in
  let center_instructions =
    candle_action296_instruction_profile_list
      variant.variant_program_representation_term and
      box_instructions =
        candle_action296_instruction_profile_list
          candle_action296_fixed_algebraic_box_program in
  let rec run index centers whole_boxes current_stack =
    match centers,whole_boxes with
    | [],[] ->
        print_endline
          "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_NO_DOMAIN_LOSS"
    | center_instruction :: center_tail,
      box_instruction :: box_tail ->
        let use_fixed =
          if List.exists
               (fun instruction ->
                 let opcode,_ =
                   candle_action296_instruction_profile_opcode instruction in
                 opcode = "sqrt" || opcode = "inv" || opcode = "atn" ||
                 opcode = "pi-half")
               center_tail then
            `Cexp_num 0`
          else
            `Cexp_num 1` in
        let next_stack =
          rand
            (concl
              (candle_action296_fixed_algebraic_compute
                candle_action296_fixed_algebraic_new_eqs
                (list_mk_comb
                  (`candle_cv_fsa_program_step`,
                   [center_boxes;boxes;radii;use_fixed;
                    center_instruction;box_instruction;current_stack])))) in
        let item =
          candle_action296_instruction_profile_top next_stack in
        let tag,domain =
          candle_action296_fixed_algebraic_item_tag_domain item in
        if aconv domain `Cexp_num 0` then
          let opcode,_ =
            candle_action296_instruction_profile_opcode
              center_instruction in
          print_endline
            ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_FIRST_DOMAIN_LOSS" ^
             " index=" ^ string_of_int index ^
             " opcode=" ^ opcode ^
             " tag=" ^ Num.string_of_num tag ^
             " domain=" ^ string_of_term domain)
        else
          run (index + 1) center_tail box_tail next_stack
    | _ ->
        failwith
          "action296 fixed algebraic: program length mismatch in trace" in
  run 0 center_instructions box_instructions `Cexp_num 0`;;

let candle_action296_fixed_algebraic_tail_comparison
      (variant,lower,upper) =
  let boxes =
    rand
      (concl
        (candle_q_dim_analytic_jet_boxes_encode_conv
          (candle_poly_fixture_q_boxes lower upper))) in
  let center_boxes =
    rand
      (concl
        (candle_action296_fixed_algebraic_compute
          candle_action296_fixed_algebraic_new_eqs
          (mk_comb (`candle_cv_q_center_environment_list`,boxes)))) in
  let radii =
    rand
      (concl
        (candle_action296_fixed_algebraic_compute
          candle_action296_fixed_algebraic_new_eqs
          (mk_comb
            (`candle_cv_q_fixed_list_round_upper`,
             mk_comb (`candle_cv_q_radius_list`,boxes))))) in
  let center_instructions =
    candle_action296_instruction_profile_list
      variant.variant_program_representation_term and
      box_instructions =
        candle_action296_instruction_profile_list
          candle_action296_fixed_algebraic_box_program in
  let rec run index centers whole_boxes old_stack new_stack =
    match centers,whole_boxes with
    | [],[] -> ()
    | center_instruction :: center_tail,
      box_instruction :: box_tail ->
        let use_fixed =
          if List.exists
               (fun instruction ->
                 let opcode,_ =
                   candle_action296_instruction_profile_opcode instruction in
                 opcode = "sqrt" || opcode = "inv" || opcode = "atn" ||
                 opcode = "pi-half")
               center_tail then
            `Cexp_num 0`
          else
            `Cexp_num 1` in
        let old_next =
          rand
            (concl
              (candle_action296_fixed_algebraic_compute
                candle_action296_fixed_algebraic_old_eqs
                (list_mk_comb
                  (`candle_cv_fs_q_dim_taylor_model_program_step`,
                   [center_boxes;boxes;radii;
                    center_instruction;box_instruction;old_stack])))) and
            new_next =
              rand
                (concl
                  (candle_action296_fixed_algebraic_compute
                    candle_action296_fixed_algebraic_new_eqs
                    (list_mk_comb
                      (`candle_cv_fsa_program_step`,
                       [center_boxes;boxes;radii;use_fixed;
                        center_instruction;box_instruction;new_stack])))) in
        let _ =
          if index >= 37 then
            let opcode,_ =
              candle_action296_instruction_profile_opcode
                center_instruction in
            let old_result =
              candle_action296_instruction_profile_top old_next and
                new_item =
                  candle_action296_instruction_profile_top new_next in
            let new_result =
              candle_action296_fixed_algebraic_item_payload new_item in
            let old_domain,old_upper =
              candle_action296_fixed_algebraic_domain_upper old_result and
                new_domain,new_upper =
                  candle_action296_fixed_algebraic_domain_upper new_result in
            print_endline
              ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_TAIL" ^
               " index=" ^ string_of_int index ^
               " opcode=" ^ opcode ^
               " old_domain=" ^ string_of_term old_domain ^
               " new_domain=" ^ string_of_term new_domain ^
               " old_upper=" ^ string_of_term old_upper ^
               " new_upper=" ^ string_of_term new_upper)
          else () in
        run (index + 1) center_tail box_tail old_next new_next
    | _ ->
        failwith
          "action296 fixed algebraic: program length mismatch in tail trace" in
  run 0 center_instructions box_instructions
    `Cexp_num 0` `Cexp_num 0`;;

let rec candle_action296_fixed_algebraic_report index = function
  | [] -> ()
  | case :: remaining ->
      let old_domain,old_upper =
        candle_action296_fixed_algebraic_result_summary
          candle_action296_fixed_algebraic_old_eqs
          `candle_cv_fs_q_dim_taylor_model_program` case in
      let new_domain,new_upper =
        candle_action296_fixed_algebraic_result_summary
          candle_action296_fixed_algebraic_new_eqs
          `candle_cv_fsa_program` case in
      print_endline
        ("CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_BOX box=" ^
         string_of_int index ^
         " old_domain=" ^ string_of_term old_domain ^
         " new_domain=" ^ string_of_term new_domain ^
         " old_upper=" ^ string_of_term old_upper ^
         " new_upper=" ^ string_of_term new_upper);
      candle_action296_fixed_algebraic_report
        (index + 1) remaining;;

let _ =
  if not
       (aconv candle_action296_fixed_algebraic_new_count `Cexp_num 8`) then
    (candle_action296_fixed_algebraic_report 1
       candle_action296_instruction_profile_cases;
     match candle_action296_instruction_profile_cases with
     | first_case :: _ ->
         candle_action296_fixed_algebraic_first_domain_loss first_case;
         candle_action296_fixed_algebraic_tail_comparison first_case
     | [] ->
         failwith "action296 fixed algebraic: missing diagnostic case");;

let candle_action296_fixed_algebraic_axioms_after = axioms ();;

if length candle_action296_instruction_profile_cases <> 8 ||
   hyp candle_action296_fixed_algebraic_old_result <> [] ||
   hyp candle_action296_fixed_algebraic_new_result <> [] ||
   not (aconv candle_action296_fixed_algebraic_old_count `Cexp_num 8`) ||
   not (aconv candle_action296_fixed_algebraic_new_count `Cexp_num 8`) ||
   length candle_action296_fixed_algebraic_axioms_after <>
     length candle_action296_fixed_algebraic_axioms_before ||
   not
     (List.for_all
       (fun theorem ->
         List.mem theorem candle_action296_fixed_algebraic_axioms_before)
       candle_action296_fixed_algebraic_axioms_after) then
  failwith "action296 fixed algebraic: final validation failed";;

let _ =
  candle_action296_fixed_algebraic_marker
    "batch" "profiled-run" "end";;

print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_RESULT boxes=8 old_accepted=8 new_accepted=8";;
print_endline
  "CANDLE_CV_ACTION296_FIXED_ALGEBRAIC_OK DEVELOPMENT_NON_RELEASE";;
