(* ========================================================================== *)
(* Fixed-scale checks for all 16 leaves of one genuine Flyspeck inequality.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Source reification and the exact captured box *)
(* identities are shared with the established genuine-leaf fixture.  Each    *)
(* recurring check has one compact computed boundary and is discharged by    *)
(* the general fixed-scale acceptance theorem.                               *)
(* ========================================================================== *)

needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_batch.ml";;
needs "candle/cv_compute_analytic_expr_fixed_scale_accept.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_analytic_expr_fixed_scale_accept;;
open Candle_cv_real_flyspeck_leaf_jet_batch_test;;

module Candle_cv_real_flyspeck_leaf_fixed_batch_test = struct

let candle_real_fixed_batch_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_real_fixed_batch_suc_one = SYM ONE;;
let candle_real_fixed_batch_dim_six = DIMINDEX_CONV `dimindex (:6)`;;
let candle_real_fixed_batch_sound_six =
  REWRITE_RULE
    [candle_real_fixed_batch_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_fs_poly_numerical_accept_sound);;

let candle_real_fixed_batch_marker index phase event =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_BATCH box=" ^ string_of_int index ^
     " phase=" ^ phase ^ " event=" ^ event);;

(* A timing-only aggregate keeps all recurring checks inside one evaluator   *)
(* call.  The individually checked results below remain the proof authority; *)
(* this count discriminates evaluator-entry cost without adding an authority. *)

let candle_cv_real_fixed_batch_accept_count_def = define
 `(candle_cv_real_fixed_batch_accept_count program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_real_fixed_batch_accept_count program (Cexp_pair boxes rest) =
     Cexp_add
       (Cexp_fst (candle_cv_fs_poly_check program boxes))
       (candle_cv_real_fixed_batch_accept_count program rest))`;;

let candle_cv_real_fixed_batch_results_def = define
 `(candle_cv_real_fixed_batch_results program (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_real_fixed_batch_results program (Cexp_pair boxes rest) =
     Cexp_pair
       (candle_cv_fs_poly_check program boxes)
       (candle_cv_real_fixed_batch_results program rest))`;;

let candle_cv_real_fixed_batch_accept_count_compute = prove
 (`!program cases.
     candle_cv_real_fixed_batch_accept_count program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_add
         (Cexp_fst
           (candle_cv_fs_poly_check program (Cexp_fst cases)))
         (candle_cv_real_fixed_batch_accept_count
           program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_real_fixed_batch_accept_count_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_real_fixed_batch_results_compute = prove
 (`!program cases.
     candle_cv_real_fixed_batch_results program cases =
     Cexp_if (Cexp_ispair cases)
       (Cexp_pair
         (candle_cv_fs_poly_check program (Cexp_fst cases))
         (candle_cv_real_fixed_batch_results
           program (Cexp_snd cases)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `cases:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_real_fixed_batch_results_def;
              cexp_if_def; cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_real_fixed_batch_compute_eqs =
  union candle_cv_fs_poly_compute_eqs
    [SPEC_ALL candle_cv_real_fixed_batch_accept_count_compute;
     SPEC_ALL candle_cv_real_fixed_batch_results_compute];;

let candle_real_fixed_batch_check_box index (lower,upper) =
  let box_md5 = candle_real_jet_batch_box_md5 lower upper in
  if box_md5 <> List.nth candle_real_jet_batch_expected_box_md5s index then
    failwith "fixed batch captured box identity mismatch";
  candle_real_fixed_batch_marker index "box-prepare" "begin";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_rep = candle_real_jet_batch_boxes_encode_conv boxes in
  let boxes_rep_tm = rand (concl boxes_rep) in
  candle_real_fixed_batch_marker index "box-prepare" "end";

  candle_real_fixed_batch_marker index "computed-check" "begin";
  let compute_th =
    compute candle_cv_fs_poly_compute_eqs
      (list_mk_comb
        (`candle_cv_fs_poly_check`,
         [candle_real_jet_batch_program_rep_tm;boxes_rep_tm])) in
  candle_real_fixed_batch_marker index "computed-check" "end";
  if hyp compute_th <> [] then
    failwith "fixed batch compute theorem has assumptions";
  let computed_pair = rand (concl compute_th) in
  let computed_verdict,_ = candle_real_jet_batch_dest_pair computed_pair in
  if not (aconv computed_verdict `Cexp_num 1`) then
    failwith ("fixed batch box " ^ string_of_int index ^ " rejected");

  candle_real_fixed_batch_marker index "theorem-handoff" "begin";
  let correctness =
    SPECL
      [candle_real_jet_batch_expression;boxes]
      candle_cv_fs_poly_check_correct in
  let abstract_compute_th =
    let th =
      PURE_REWRITE_RULE
        [SYM candle_real_jet_batch_program_rep;SYM boxes_rep]
        compute_th in
    PURE_REWRITE_RULE [SYM candle_real_jet_batch_compile_th] th in
  if not
      (aconv (lhand (concl abstract_compute_th))
             (lhand (concl correctness))) then
    failwith "fixed batch abstract/concrete checker lhs mismatch";
  let accept_encoding_th = TRANS (SYM abstract_compute_th) correctness in
  let numerical_goal =
    list_mk_comb
      (`candle_fs_poly_numerical_accept`,
       [candle_real_jet_batch_expression;boxes]) in
  let flag_num_th =
    REWRITE_RULE
      [cexp_fst_def; candle_real_fixed_batch_suc_one;
       injectivity "cval"]
      (AP_TERM `Cexp_fst` accept_encoding_th) in
  let expected_flag =
    mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
  let flag_num_th =
    if aconv (concl flag_num_th) expected_flag then flag_num_th
    else if aconv (concl flag_num_th)
              (mk_eq (rand expected_flag,lhand expected_flag)) then
      SYM flag_num_th
    else failwith "fixed batch numerical flag theorem mismatch" in
  let numerical_th =
    MATCH_MP
      (SPEC numerical_goal candle_real_fixed_batch_flag_accept)
      flag_num_th in
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
        candle_real_fixed_batch_sound_six)
      (CONJ candle_real_jet_batch_valid
        (CONJ length_six numerical_th)) in
  let source_th =
    REWRITE_RULE [candle_real_jet_batch_source_th] vector_th in
  let p,body = dest_forall (concl source_th) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source = dest_comb partial in
  if hyp numerical_th <> [] || hyp vector_th <> [] || hyp source_th <> [] ||
     not (aconv p candle_real_jet_batch_vector) ||
     not (aconv relation candle_real_jet_batch_real_lt) ||
     not (aconv source candle_real_jet_batch_source) ||
     not (aconv zero candle_real_jet_batch_real_zero) then
    failwith "fixed batch source theorem mismatch";
  candle_real_fixed_batch_marker index "theorem-handoff" "end";
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_BATCH_RESULT box=" ^
     string_of_int index ^ " verdict=accept box_md5=" ^ box_md5 ^
     " theorem_md5=" ^
     Digest.to_hex (Digest.string (string_of_thm source_th)));
  source_th;;

let candle_real_fixed_batch_theorems =
  map2 candle_real_fixed_batch_check_box
    (0--15) candle_real_jet_batch_box_sources;;

let candle_real_fixed_batch_boxes_rep_terms =
  map
    (fun (lower,upper) ->
      let boxes = candle_poly_fixture_q_boxes lower upper in
      rand (concl (candle_real_jet_batch_boxes_encode_conv boxes)))
    candle_real_jet_batch_box_sources;;

let candle_real_fixed_batch_boxes_rep_list =
  itlist
    (fun boxes rest -> list_mk_comb (`Cexp_pair`,[boxes;rest]))
    candle_real_fixed_batch_boxes_rep_terms `Cexp_num 0`;;

let _ =
  candle_real_fixed_batch_marker (-1) "batched-full-results" "begin";;

let candle_real_fixed_batch_results_th =
  compute candle_cv_real_fixed_batch_compute_eqs
    (list_mk_comb
      (`candle_cv_real_fixed_batch_results`,
       [candle_real_jet_batch_program_rep_tm;
        candle_real_fixed_batch_boxes_rep_list]));;

let _ =
  candle_real_fixed_batch_marker (-1) "batched-full-results" "end";;

let rec candle_real_fixed_batch_dest_cval_list tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_num` then []
  else if aconv operator `Cexp_pair` then
    match arguments with
    | [head;tail] ->
        head :: candle_real_fixed_batch_dest_cval_list tail
    | _ -> failwith "fixed batch malformed computed result list"
  else failwith "fixed batch expected concrete computed result list";;

let candle_real_fixed_batch_results =
  candle_real_fixed_batch_dest_cval_list
    (rand (concl candle_real_fixed_batch_results_th));;

let candle_real_fixed_batch_results_accepted =
  List.for_all
    (fun result ->
      let verdict,_ = candle_real_jet_batch_dest_pair result in
      aconv verdict `Cexp_num 1`)
    candle_real_fixed_batch_results;;

let _ =
  candle_real_fixed_batch_marker (-1) "batched-computed-check" "begin";;

let candle_real_fixed_batch_accept_count_th =
  compute candle_cv_real_fixed_batch_compute_eqs
    (list_mk_comb
      (`candle_cv_real_fixed_batch_accept_count`,
       [candle_real_jet_batch_program_rep_tm;
        candle_real_fixed_batch_boxes_rep_list]));;

let _ =
  candle_real_fixed_batch_marker (-1) "batched-computed-check" "end";;

if length candle_real_fixed_batch_theorems <> 16 ||
   hyp candle_real_fixed_batch_results_th <> [] ||
   length candle_real_fixed_batch_results <> 16 ||
   not candle_real_fixed_batch_results_accepted ||
   hyp candle_real_fixed_batch_accept_count_th <> [] ||
   not (aconv (rand (concl candle_real_fixed_batch_accept_count_th))
          `Cexp_num 16`) ||
   hyp candle_real_jet_batch_valid <> [] ||
   hyp candle_real_jet_batch_source_th <> [] ||
   hyp candle_real_jet_batch_run_th <> [] then
  failwith "fixed batch result count or source assumptions drift";;

let _ =
  print_endline
    "CANDLE_CV_REAL_FLYSPECK_FIXED_BATCH_STATS programs=1 boxes=16 accepted=16 batched_full_results=16 batched_accept_count=16";;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_FIXED_BATCH_OK";;

end;;
