(* ========================================================================== *)
(* One-verdict fixed-scale proof batch for a genuine Flyspeck inequality.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  One compiled source program and all 16 exact *)
(* captured leaf boxes are checked in one Kernel.compute call.  General      *)
(* batch correctness and membership laws derive each source theorem from    *)
(* that single compact verdict.                                              *)
(* ========================================================================== *)

needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_batch.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_accept.ml";;

open Candle_cv_exact_interval_program;;
open Candle_cv_analytic_expr_fixed_scale_accept;;
open Candle_cv_real_flyspeck_leaf_jet_batch_test;;

module Candle_cv_real_flyspeck_leaf_fixed_proved_batch_test = struct

let candle_real_fixed_proved_batch_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_real_fixed_proved_batch_dim_six =
  DIMINDEX_CONV `dimindex (:6)`;;

let candle_real_fixed_proved_batch_sound_six =
  REWRITE_RULE
    [candle_real_fixed_proved_batch_dim_six]
    (INST_TYPE [`:6`,`:N`] candle_fs_poly_numerical_accept_sound);;

let candle_real_fixed_proved_batch_marker phase event =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_BATCH phase=" ^ phase ^
     " event=" ^ event);;

let candle_real_fixed_proved_batch_cval_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_real_fixed_proved_batch_cval_list items =
  itlist candle_real_fixed_proved_batch_cval_pair items `Cexp_num 0`;;

let _ =
  candle_real_fixed_proved_batch_marker "box-prepare" "begin";;

let candle_real_fixed_proved_batch_prepared =
  map2
    (fun index (lower,upper) ->
      let box_md5 = candle_real_jet_batch_box_md5 lower upper in
      if box_md5 <> List.nth candle_real_jet_batch_expected_box_md5s index then
        failwith "fixed proved batch captured box identity mismatch";
      let boxes = candle_poly_fixture_q_boxes lower upper in
      let representation =
        candle_real_jet_batch_boxes_encode_conv boxes in
      boxes,representation,rand (concl representation),box_md5)
    (0--15) candle_real_jet_batch_box_sources;;

let candle_real_fixed_proved_batch_boxes =
  mk_list
    (map (fun (boxes,_,_,_) -> boxes)
       candle_real_fixed_proved_batch_prepared,
     type_of
       (let boxes,_,_,_ = hd candle_real_fixed_proved_batch_prepared in
        boxes));;

let candle_real_fixed_proved_batch_encoded_boxes =
  candle_real_fixed_proved_batch_cval_list
    (map (fun (_,_,encoded,_) -> encoded)
       candle_real_fixed_proved_batch_prepared);;

let candle_real_fixed_proved_batch_boxes_encoding =
  REWRITE_CONV
    (candle_cv_fs_poly_batch_boxes_def ::
     map (fun (_,representation,_,_) -> representation)
       candle_real_fixed_proved_batch_prepared)
    (mk_comb
      (`candle_cv_fs_poly_batch_boxes`,
       candle_real_fixed_proved_batch_boxes));;

let candle_real_fixed_proved_batch_program_encoding =
  TRANS
    (AP_TERM `candle_cv_q_instruction_list`
      candle_real_jet_batch_compile_th)
    candle_real_jet_batch_program_rep;;

let _ =
  if hyp candle_real_fixed_proved_batch_boxes_encoding <> [] ||
     hyp candle_real_fixed_proved_batch_program_encoding <> [] ||
     not
       (aconv
         (rand (concl candle_real_fixed_proved_batch_boxes_encoding))
         candle_real_fixed_proved_batch_encoded_boxes) then
    failwith "fixed proved batch encoding mismatch";;

let _ =
  candle_real_fixed_proved_batch_marker "box-prepare" "end";;

let candle_real_fixed_proved_batch_concrete_call =
  list_mk_comb
    (`candle_cv_fs_poly_batch_check`,
     [candle_real_jet_batch_program_rep_tm;
      candle_real_fixed_proved_batch_encoded_boxes]);;

let _ =
  candle_real_fixed_proved_batch_marker "computed-check" "begin";;

let candle_real_fixed_proved_batch_compute_th =
  compute candle_cv_fs_poly_batch_compute_eqs
    candle_real_fixed_proved_batch_concrete_call;;

let _ =
  candle_real_fixed_proved_batch_marker "computed-check" "end";;

let _ =
  if hyp candle_real_fixed_proved_batch_compute_th <> [] ||
     not
       (aconv (rand (concl candle_real_fixed_proved_batch_compute_th))
          `Cexp_num 1`) then
    failwith "fixed proved batch rejected";;

let _ =
  candle_real_fixed_proved_batch_marker "theorem-handoff" "begin";;

let candle_real_fixed_proved_batch_abstract_compute_th =
  PURE_REWRITE_RULE
    [SYM candle_real_fixed_proved_batch_program_encoding;
     SYM candle_real_fixed_proved_batch_boxes_encoding]
    candle_real_fixed_proved_batch_compute_th;;

let candle_real_fixed_proved_batch_correctness =
  SPECL
    [candle_real_fixed_proved_batch_boxes;
     candle_real_jet_batch_expression]
    candle_cv_fs_poly_batch_check_correct;;

let _ =
  if not
      (aconv
        (lhand (concl candle_real_fixed_proved_batch_abstract_compute_th))
        (lhand (concl candle_real_fixed_proved_batch_correctness))) then
    failwith "fixed proved batch abstract checker mismatch";;

let candle_real_fixed_proved_batch_accept_encoding =
  TRANS
    (SYM candle_real_fixed_proved_batch_abstract_compute_th)
    candle_real_fixed_proved_batch_correctness;;

let candle_real_fixed_proved_batch_numerical_goal =
  list_mk_comb
    (`candle_fs_poly_batch_numerical_accept`,
     [candle_real_jet_batch_expression;
      candle_real_fixed_proved_batch_boxes]);;

let candle_real_fixed_proved_batch_flag_th =
  let th =
    REWRITE_RULE
      [injectivity "cval"; SYM ONE]
      candle_real_fixed_proved_batch_accept_encoding in
  let expected =
    mk_eq
      (`1`,
       mk_cond
         (candle_real_fixed_proved_batch_numerical_goal,`1`,`0`)) in
  if aconv (concl th) expected then th
  else if aconv (concl th) (mk_eq (rand expected,lhand expected)) then
    SYM th
  else failwith "fixed proved batch flag mismatch";;

let candle_real_fixed_proved_batch_accept_th =
  MATCH_MP
    (SPEC
      candle_real_fixed_proved_batch_numerical_goal
      candle_real_fixed_proved_batch_flag_accept)
    candle_real_fixed_proved_batch_flag_th;;

(* The general membership law remains the public arbitrary-list interface.   *)
(* For this concrete batch, expand its recursive conjunction once rather than *)
(* repeatedly normalizing sixteen separate MEM propositions.                 *)

let candle_real_fixed_proved_batch_individual_accepts =
  CONJUNCTS
    (REWRITE_RULE
      [candle_fs_poly_batch_numerical_accept_def]
      candle_real_fixed_proved_batch_accept_th);;

let candle_real_fixed_proved_batch_member_source index
    (boxes,_,_,box_md5) =
  let numerical_th =
    List.nth candle_real_fixed_proved_batch_individual_accepts index in
  let expected_numerical =
    list_mk_comb
      (`candle_fs_poly_numerical_accept`,
       [candle_real_jet_batch_expression;boxes]) in
  if not (aconv (concl numerical_th) expected_numerical) then
    failwith "fixed proved batch conjunction order mismatch";
  let length_six =
    prove
      (mk_eq
        (mk_comb
          (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,boxes),
         `6`),
       REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV) in
  let vector_th =
    MATCH_MP
      (SPECL
        [candle_real_jet_batch_expression;boxes]
        candle_real_fixed_proved_batch_sound_six)
      (CONJ candle_real_jet_batch_valid
        (CONJ length_six numerical_th)) in
  let source_th =
    REWRITE_RULE [candle_real_jet_batch_source_th] vector_th in
  if hyp numerical_th <> [] || hyp vector_th <> [] || hyp source_th <> [] then
    failwith "fixed proved batch source theorem assumptions";
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_BATCH_RESULT box=" ^
     string_of_int index ^ " verdict=accept box_md5=" ^ box_md5 ^
     " theorem_md5=" ^
     Digest.to_hex (Digest.string (string_of_thm source_th)));
  source_th;;

let candle_real_fixed_proved_batch_theorems =
  map2 candle_real_fixed_proved_batch_member_source
    (0--15) candle_real_fixed_proved_batch_prepared;;

let _ =
  candle_real_fixed_proved_batch_marker "theorem-handoff" "end";;

if length candle_real_fixed_proved_batch_theorems <> 16 ||
   length candle_real_fixed_proved_batch_individual_accepts <> 16 ||
   hyp candle_real_fixed_proved_batch_accept_th <> [] ||
   hyp candle_real_jet_batch_valid <> [] ||
   hyp candle_real_jet_batch_source_th <> [] ||
   hyp candle_real_jet_batch_run_th <> [] then
  failwith "fixed proved batch result count or source assumptions drift";;

let _ =
  print_endline
    "CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_BATCH_STATS programs=1 boxes=16 computed_verdicts=1 accepted=16";;

let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_BATCH_OK";;

end;;
