(* ========================================================================== *)
(* Direct root theorem from one fixed batch verdict and reusable geometry.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The 16-leaf split tree proves only that its   *)
(* exact boxes cover the root.  The general fixed-batch soundness theorem    *)
(* then turns one numerical verdict plus that reusable coverage fact into    *)
(* the source inequality over the root, without constructing numerical       *)
(* source theorems at every leaf.                                             *)
(* ========================================================================== *)

needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_fixed_proved_batch.ml";;
needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_certificate.ml";;

open Candle_cv_analytic_expr_fixed_scale_accept;;
open Candle_cv_real_flyspeck_leaf_jet_batch_test;;
open Candle_cv_real_flyspeck_leaf_fixed_proved_batch_test;;
open Candle_cv_real_flyspeck_leaf_jet_certificate_test;;

module Candle_cv_real_flyspeck_leaf_fixed_proved_cover_test = struct

let candle_real_fixed_proved_cover_marker phase event =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_COVER phase=" ^ phase ^
     " event=" ^ event);;

let candle_real_fixed_proved_cover_predicate =
  vsubst
    [candle_real_fixed_proved_batch_boxes,
     `batch:((((num#num)#num)#((num#num)#num))list)list`]
    `\p:real^6.
       ?boxes. MEM boxes batch /\
         p IN interval
           [candle_q_box_lower_vector boxes,
            candle_q_box_upper_vector boxes]`;;

let candle_real_fixed_proved_cover_memberships =
  map
    (fun (boxes,_,_,_) ->
      EQT_ELIM
        (REWRITE_CONV [MEM]
          (list_mk_comb
            (`MEM:(((num#num)#num)#((num#num)#num))list->
                  ((((num#num)#num)#((num#num)#num))list)list->bool`,
             [boxes;candle_real_fixed_proved_batch_boxes]))))
    candle_real_fixed_proved_batch_prepared;;

let candle_real_fixed_proved_cover_leaf index =
  let boxes,_,_,_ =
    List.nth candle_real_fixed_proved_batch_prepared index in
  let membership =
    List.nth candle_real_fixed_proved_cover_memberships index in
  let lower_eq,upper_eq =
    List.nth candle_real_jet_certificate_leaf_vector_equalities index in
  let point = `p:real^6` in
  let predicate_application =
    mk_comb (candle_real_fixed_proved_cover_predicate,point) in
  let predicate_beta = BETA_CONV predicate_application in
  let existential = rand (concl predicate_beta) in
  let bound_boxes,body = dest_exists existential in
  let witness_body = vsubst [boxes,bound_boxes] body in
  let witness_membership,domain = dest_conj witness_body in
  if not (aconv witness_membership (concl membership)) then
    failwith "fixed proved cover membership shape mismatch";
  let raw_goal =
    mk_forall (point,mk_imp (domain,predicate_application)) in
  let raw_leaf_th =
    candle_real_jet_certificate_debug_prove "fixed-cover-leaf" raw_goal
      (BETA_TAC THEN X_GEN_TAC `p:real^6` THEN DISCH_TAC THEN
       EXISTS_TAC boxes THEN CONJ_TAC THENL
       [ACCEPT_TAC membership; FIRST_ASSUM MATCH_ACCEPT_TAC]) in
  REWRITE_RULE [lower_eq;upper_eq] raw_leaf_th;;

let _ = candle_real_fixed_proved_cover_marker "leaf-coverage" "begin";;

let candle_real_fixed_proved_cover_leaf_passes =
  map candle_real_fixed_proved_cover_leaf (0--15);;

let _ = candle_real_fixed_proved_cover_marker "leaf-coverage" "end";;

let _ = candle_real_fixed_proved_cover_marker "tree-coverage" "begin";;

let rec candle_real_fixed_proved_cover_assemble tree =
  match tree with
  | Candle_real_jet_leaf index ->
      List.nth candle_real_fixed_proved_cover_leaf_passes index
  | Candle_real_jet_glue (index,left,right) ->
      let left_th = candle_real_fixed_proved_cover_assemble left in
      let right_th = candle_real_fixed_proved_cover_assemble right in
      candle_real_jet_certificate_glue index left_th right_th;;

let candle_real_fixed_proved_cover_root_pass =
  BETA_RULE
    (candle_real_fixed_proved_cover_assemble
      candle_real_jet_certificate_tree);;

let _ = candle_real_fixed_proved_cover_marker "tree-coverage" "end";;

let _ = candle_real_fixed_proved_cover_marker "root-coverage" "begin";;

let candle_real_fixed_proved_cover_root_lower_source,_ =
  hd candle_real_jet_batch_box_sources;;

let _,candle_real_fixed_proved_cover_root_upper_source =
  List.nth candle_real_jet_batch_box_sources 15;;

let candle_real_fixed_proved_cover_root_boxes =
  candle_poly_fixture_q_boxes
    candle_real_fixed_proved_cover_root_lower_source
    candle_real_fixed_proved_cover_root_upper_source;;

let candle_real_fixed_proved_cover_root_equalities =
  candle_real_jet_certificate_leaf_equalities
    (candle_real_fixed_proved_cover_root_lower_source,
     candle_real_fixed_proved_cover_root_upper_source);;

let candle_real_fixed_proved_cover_root_lower_eq,
    candle_real_fixed_proved_cover_root_upper_eq =
  candle_real_fixed_proved_cover_root_equalities;;

let candle_real_fixed_proved_cover_goal =
  vsubst
    [candle_real_fixed_proved_cover_root_boxes,
     `root_boxes:(((num#num)#num)#((num#num)#num))list`;
     candle_real_fixed_proved_batch_boxes,
     `batch:((((num#num)#num)#((num#num)#num))list)list`]
    `candle_fs_poly_batch_covers (ARB:real^6) root_boxes batch`;;

let candle_real_fixed_proved_cover_expansion =
  REWRITE_CONV
    [candle_fs_poly_batch_covers_def;
     candle_real_fixed_proved_cover_root_lower_eq;
     candle_real_fixed_proved_cover_root_upper_eq]
    candle_real_fixed_proved_cover_goal;;

let candle_real_fixed_proved_cover_th =
  let expected = rand (concl candle_real_fixed_proved_cover_expansion) in
  if not
      (aconv (concl candle_real_fixed_proved_cover_root_pass) expected) then
    failwith "fixed proved cover root shape mismatch";
  EQ_MP
    (SYM candle_real_fixed_proved_cover_expansion)
    candle_real_fixed_proved_cover_root_pass;;

let _ = candle_real_fixed_proved_cover_marker "root-coverage" "end";;

let _ = candle_real_fixed_proved_cover_marker "box-lengths" "begin";;

let candle_real_fixed_proved_cover_lengths =
  let boxes =
    `boxes:(((num#num)#num)#((num#num)#num))list` in
  let goal =
    mk_forall
      (boxes,
       mk_imp
         (list_mk_comb
           (`MEM:(((num#num)#num)#((num#num)#num))list->
                 ((((num#num)#num)#((num#num)#num))list)list->bool`,
            [boxes;candle_real_fixed_proved_batch_boxes]),
          mk_eq
            (mk_comb
              (`LENGTH:(((num#num)#num)#((num#num)#num))list->num`,
               boxes),
             `6`))) in
  prove
    (goal,
     REWRITE_TAC[MEM] THEN REPEAT STRIP_TAC THEN
     ASM_REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

let _ = candle_real_fixed_proved_cover_marker "box-lengths" "end";;

let candle_real_fixed_proved_cover_batch_sound_six =
  REWRITE_RULE
    [candle_real_fixed_proved_batch_dim_six]
    (INST_TYPE [`:6`,`:N`] candle_fs_poly_batch_sound);;

let _ = candle_real_fixed_proved_cover_marker "root-handoff" "begin";;

let candle_real_fixed_proved_cover_vector_th =
  MATCH_MP
    (SPECL
      [candle_real_jet_batch_expression;
       candle_real_fixed_proved_cover_root_boxes;
       candle_real_fixed_proved_batch_boxes;
       `ARB:real^6`]
      candle_real_fixed_proved_cover_batch_sound_six)
    (CONJ candle_real_jet_batch_valid
      (CONJ candle_real_fixed_proved_batch_accept_th
        (CONJ candle_real_fixed_proved_cover_lengths
          candle_real_fixed_proved_cover_th)));;

let candle_real_fixed_proved_cover_root_theorem =
  REWRITE_RULE
    [candle_real_jet_batch_source_th;
     candle_real_fixed_proved_cover_root_lower_eq;
     candle_real_fixed_proved_cover_root_upper_eq]
    candle_real_fixed_proved_cover_vector_th;;

let _ = candle_real_fixed_proved_cover_marker "root-handoff" "end";;

if length candle_real_fixed_proved_cover_leaf_passes <> 16 ||
   hyp candle_real_fixed_proved_cover_th <> [] ||
   hyp candle_real_fixed_proved_cover_lengths <> [] ||
   hyp candle_real_fixed_proved_cover_vector_th <> [] ||
   hyp candle_real_fixed_proved_cover_root_theorem <> [] ||
   not
     (aconv (concl candle_real_fixed_proved_cover_root_theorem)
        (concl candle_real_jet_certificate_root_theorem)) then
  failwith "fixed proved cover root theorem drift";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_COVER_RESULT " ^
     "verdicts=1 leaves=16 coverage_glues=15 source_leaf_theorems=0 " ^
     "theorem_md5=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm candle_real_fixed_proved_cover_root_theorem)));;

let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_COVER_OK";;

end;;
