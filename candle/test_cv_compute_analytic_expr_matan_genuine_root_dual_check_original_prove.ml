(* ========================================================================== *)
(* Source-level theorem from the retained genuine composite [matan] verdict. *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare.ml";;

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_sound;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_center_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_root_dual_check_original_prove = struct

let axioms_before = axioms ();;
let started = Unix.gettimeofday ();;

let erased_center =
  mk_comb (`candle_analytic_erase_sqrt_certificates`,center_expression);;
let erased_box =
  mk_comb (`candle_analytic_erase_sqrt_certificates`,tight_expression);;
let erasure_theorem =
  REWRITE_CONV
    [candle_analytic_erase_sqrt_certificates_def]
    (mk_eq (erased_center,erased_box));;
let erasure_equality =
  if hyp erasure_theorem = [] && rand (concl erasure_theorem) = `T`
  then EQT_ELIM erasure_theorem
  else failwith "genuine matan dual proof: erased source mismatch";;

let center_program_encoding =
  TRANS
    (AP_TERM `candle_cv_analytic_instruction_list` center_compile_theorem)
    center_program_representation;;
let box_program_encoding =
  TRANS
    (AP_TERM `candle_cv_analytic_instruction_list` tight_compile_theorem)
    tight_program_representation;;

let rec congr_apps function_theorem arguments =
  match arguments with
  | [] -> function_theorem
  | argument_theorem :: remaining ->
      congr_apps (MK_COMB (function_theorem,argument_theorem)) remaining;;

let call_encoding =
  congr_apps
    (REFL `candle_cv_matan_fs_taylor_dual_check`)
    [center_program_encoding;box_program_encoding;boxes_representation];;
let flag_call_encoding = AP_TERM `Cexp_fst` call_encoding;;
let abstract_compute_theorem =
  TRANS flag_call_encoding compute_theorem;;

let correctness =
  SPECL [center_expression;tight_expression;boxes]
    candle_cv_matan_fs_taylor_dual_check_correct;;
if not
    (aconv (lhand (concl abstract_compute_theorem))
       (lhand (concl correctness))) then
  failwith "genuine matan dual proof: abstract checker mismatch";;

let accept_encoding_theorem =
  TRANS (SYM abstract_compute_theorem) correctness;;
let numerical_goal =
  list_mk_comb
    (`candle_matan_fs_taylor_dual_numerical_accept`,
     [center_expression;tight_expression;boxes]);;
let flag_theorem =
  let th =
    REWRITE_RULE[injectivity "cval"; SYM ONE] accept_encoding_theorem in
  let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
  if aconv (concl th) expected then th
  else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then SYM th
  else failwith "genuine matan dual proof: numerical flag mismatch";;
let flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;
let numerical_theorem =
  MATCH_MP (SPEC numerical_goal flag_accept) flag_theorem;;

let length_six = prove
 (mk_eq
   (mk_comb
     (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
    `6`),
  REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;
let sound_six =
  REWRITE_RULE
    [DIMINDEX_CONV `dimindex (:6)`]
    (INST_TYPE
      [`:6`,`:N`]
      candle_matan_fs_taylor_dual_numerical_accept_sound);;
let vector_theorem =
  MATCH_MP
    (SPECL [center_expression;tight_expression;boxes] sound_six)
    (end_itlist CONJ
      [erasure_equality;tight_valid_theorem;length_six;numerical_theorem]);;

let denotation_term =
  mk_icomb
    (mk_icomb (`candle_analytic_denote_dim`,tight_expression),vector);;
let denotation_theorem =
  let expanded =
    REWRITE_CONV
      [candle_analytic_denote_dim_def;
       DIMINDEX_CONV `dimindex (:6)`]
      denotation_term in
  let listed = CONV_RULE (ONCE_DEPTH_CONV LIST_OF_SEQ_CONV) expanded in
  let beta = CONV_RULE (DEPTH_CONV BETA_CONV) listed in
  CONV_RULE (DEPTH_CONV NUM_ADD_CONV) beta;;
if not
    (aconv (rand (concl denotation_theorem))
       (lhand (concl tight_source_theorem))) then
  failwith "genuine matan dual proof: vector environment mismatch";;
let denotation_source_theorem =
  TRANS denotation_theorem tight_source_theorem;;
let original_theorem =
  REWRITE_RULE[denotation_source_theorem] vector_theorem;;

let point,body = dest_forall (concl original_theorem);;
let _,claim = dest_imp body;;
let partial,zero = dest_comb claim;;
let relation,source_at_point = dest_comb partial;;
let expected_source = vsubst [point,vector] source;;

let seconds = Unix.gettimeofday () -. started;;
if hyp erasure_equality <> [] || hyp numerical_theorem <> [] ||
   hyp vector_theorem <> [] || hyp original_theorem <> [] then
  failwith "genuine matan dual proof: theorem assumptions";;
if not (aconv relation `(<):real->real->bool`) ||
   not (aconv zero `&0:real`) ||
   not (aconv source_at_point expected_source) ||
   not (aconv (mk_abs (point,source_at_point)) function_term) then
  failwith "genuine matan dual proof: original source theorem mismatch";;

let axioms_after = axioms ();;
if length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan dual proof: changed the global axiom set";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_ORIGINAL_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " verdict=proved" ^
   " handoff_seconds=" ^ string_of_float seconds ^
   " theorem_chars=" ^
     string_of_int (String.length (string_of_thm original_theorem)) ^
   " assumptions=0 axiom_growth=0");;
print_endline
  "CANDLE_CV_MATAN_GENUINE_ROOT_DUAL_CHECK_ORIGINAL_OK";;

end;;
