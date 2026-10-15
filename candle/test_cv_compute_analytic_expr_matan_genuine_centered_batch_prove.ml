(* ========================================================================== *)
(* Warm proof-producing batch for one genuine Flyspeck [matan] expression.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The retained root result and three centered   *)
(* subboxes share the authenticated source and both compiled 1,429-opcode    *)
(* programs.  The subboxes have the same center as the root, so the retained *)
(* point certificates remain applicable; the whole-root square-root bounds  *)
(* are conservative for every subbox.  Each computed flag is connected to a *)
(* source-level theorem by the general dual-check soundness theorem.          *)
(* ========================================================================== *)

needs "candle/test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare.ml";;

open Candle_cv_analytic_expr_certificate_erasure;;
open Candle_cv_analytic_expr_fixed_scale_taylor_handoff_sound;;
open Test_cv_compute_analytic_expr_matan_genuine_root_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_tight_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_center_prepare;;
open Test_cv_compute_analytic_expr_matan_genuine_root_dual_check_prepare;;

module Test_cv_compute_analytic_expr_matan_genuine_centered_batch_prove = struct

let axioms_before = axioms ();;

let marker scope phase event =
  print_endline
    ("CANDLE_CERT_PROFILE lane=matan-genuine-centered-batch scope=" ^ scope ^
     " phase=" ^ phase ^ " event=" ^ event);;

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
  else failwith "genuine matan centered batch: erased source mismatch";;

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

let flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let sound_six =
  REWRITE_RULE
    [DIMINDEX_CONV `dimindex (:6)`]
    (INST_TYPE
      [`:6`,`:N`]
      candle_matan_fs_taylor_dual_numerical_accept_sound);;

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
let denotation_source_theorem =
  if aconv (rand (concl denotation_theorem))
       (lhand (concl tight_source_theorem)) then
    TRANS denotation_theorem tight_source_theorem
  else failwith "genuine matan centered batch: vector environment mismatch";;

let shrink_interval numerator denominator lo hi =
  let two = Num.num_of_int 2 in
  let center = Num.div_num (Num.add_num lo hi) two in
  let width = Num.sub_num hi lo in
  let radius =
    Num.div_num
      (Num.mul_num width (Num.num_of_int numerator))
      (Num.mul_num two (Num.num_of_int denominator)) in
  Num.sub_num center radius,Num.add_num center radius;;

let box_nums numerator denominator =
  map2 (shrink_interval numerator denominator) lower_num upper_num;;

let make_boxes intervals =
  mk_list
    (map
      (fun (lo,hi) ->
        mk_pair (candle_q_term lo,candle_q_term hi))
      intervals,
     candle_q_interval_type);;

let encode_boxes boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def; FST; SND]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let prove_from_compute scope boxes boxes_encoding concrete_compute =
  marker scope "theorem-handoff" "begin";
  let call_encoding =
    congr_apps
      (REFL `candle_cv_matan_fs_taylor_dual_check`)
      [center_program_encoding;box_program_encoding;boxes_encoding] in
  let abstract_compute =
    TRANS (AP_TERM `Cexp_fst` call_encoding) concrete_compute in
  let correctness =
    SPECL [center_expression;tight_expression;boxes]
      candle_cv_matan_fs_taylor_dual_check_correct in
  if not
      (aconv (lhand (concl abstract_compute))
         (lhand (concl correctness))) then
    failwith "genuine matan centered batch: abstract checker mismatch";
  let accept_encoding = TRANS (SYM abstract_compute) correctness in
  let numerical_goal =
    list_mk_comb
      (`candle_matan_fs_taylor_dual_numerical_accept`,
       [center_expression;tight_expression;boxes]) in
  let flag_theorem =
    let th = REWRITE_RULE[injectivity "cval"; SYM ONE] accept_encoding in
    let expected = mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
    if aconv (concl th) expected then th
    else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then
      SYM th
    else failwith "genuine matan centered batch: numerical flag mismatch" in
  let numerical_theorem =
    MATCH_MP (SPEC numerical_goal flag_accept) flag_theorem in
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let vector_theorem =
    MATCH_MP
      (SPECL [center_expression;tight_expression;boxes] sound_six)
      (end_itlist CONJ
        [erasure_equality;tight_valid_theorem;length_six;numerical_theorem]) in
  let source_theorem =
    REWRITE_RULE[denotation_source_theorem] vector_theorem in
  let point,body = dest_forall (concl source_theorem) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source_at_point = dest_comb partial in
  let expected_source = vsubst [point,vector] source in
  if hyp concrete_compute <> [] || hyp numerical_theorem <> [] ||
     hyp vector_theorem <> [] || hyp source_theorem <> [] ||
     not (aconv relation `(<):real->real->bool`) ||
     not (aconv zero `&0:real`) ||
     not (aconv source_at_point expected_source) ||
     not (aconv (mk_abs (point,source_at_point)) function_term) then
    failwith "genuine matan centered batch: source theorem mismatch";
  marker scope "theorem-handoff" "end";
  source_theorem;;

let run_computed scope numerator denominator =
  marker scope "box-encoding" "begin";
  let intervals = box_nums numerator denominator in
  let boxes = make_boxes intervals in
  let boxes_encoding = encode_boxes boxes in
  let boxes_representation_term = rand (concl boxes_encoding) in
  marker scope "box-encoding" "end";
  marker scope "composite-compute" "begin";
  let concrete_compute =
    Kernel.compute
      (COMPUTE_INIT_THMS,candle_cv_matan_fs_taylor_handoff_compute_eqs)
      (mk_comb
        (`Cexp_fst`,
         list_mk_comb
           (`candle_cv_matan_fs_taylor_dual_check`,
            [center_program_representation_term;
             box_program_representation_term;
             boxes_representation_term]))) in
  marker scope "composite-compute" "end";
  if hyp concrete_compute <> [] ||
     not (aconv (rand (concl concrete_compute)) `Cexp_num 1`) then
    failwith ("genuine matan centered batch: rejected " ^ scope);
  let source_theorem =
    prove_from_compute scope boxes boxes_encoding concrete_compute in
  print_endline
    ("CANDLE_CV_MATAN_GENUINE_CENTERED_BATCH_BOX" ^
     " DEVELOPMENT_NON_RELEASE scope=" ^ scope ^
     " radius=" ^ string_of_int numerator ^ "/" ^
       string_of_int denominator ^
     " verdict=accept theorem_chars=" ^
       string_of_int (String.length (string_of_thm source_theorem)) ^
     " assumptions=0");
  source_theorem;;

(* The root computation is retained by the editing checkpoint.  Reusing it *)
(* keeps the warm batch honest: only new recurring boxes are recomputed.     *)
let root_scope = "box-0-root-retained";;
let root_theorem =
  let theorem =
    prove_from_compute root_scope boxes boxes_representation compute_theorem in
  theorem;;

let centered_theorems =
  [run_computed "box-1-radius-3-4" 3 4;
   run_computed "box-2-radius-1-2" 1 2;
   run_computed "box-3-radius-1-4" 1 4];;

let axioms_after = axioms ();;
if length centered_theorems <> 3 || hyp root_theorem <> [] ||
   not (List.for_all (fun th -> hyp th = []) centered_theorems) ||
   length axioms_after <> length axioms_before ||
   not (List.for_all (fun th -> List.mem th axioms_before) axioms_after) then
  failwith "genuine matan centered batch: final contract mismatch";;

print_endline
  ("CANDLE_CV_MATAN_GENUINE_CENTERED_BATCH_RESULT" ^
   " DEVELOPMENT_NON_RELEASE source_id=" ^ source_id ^
   " programs=2 instructions_each=" ^ string_of_int instruction_count ^
   " boxes=4 retained=1 computed=3 accepted=4 source_theorems=4" ^
   " assumptions=0 axiom_growth=0");;
print_endline "CANDLE_CV_MATAN_GENUINE_CENTERED_BATCH_OK";;

end;;
