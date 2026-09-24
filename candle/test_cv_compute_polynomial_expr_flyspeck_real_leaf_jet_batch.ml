(* ========================================================================== *)
(* Shared-jet batch over all pass boxes of one genuine Flyspeck inequality.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The 16 boxes are exact terms captured from    *)
(* cv-nonlinear-real-leaf-batch-capture-v1-run-001.  The source is reified    *)
(* and compiled once; each box then receives a fresh computed check and an    *)
(* assumption-free source-level theorem through the universal soundness law.  *)
(* ========================================================================== *)

load_path :=
  ["/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6/formal_ineqs"] @
  !load_path;;

needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_sound.ml";;

open Candle_cv_linear_combination_core;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_jet;;
open Candle_cv_polynomial_expr_flyspeck_reify;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;
open Candle_cv_polynomial_expr_dim_jet_check;;
open Candle_cv_polynomial_expr_dim_jet_sound;;

module Candle_cv_real_flyspeck_leaf_jet_batch_test = struct

let candle_real_jet_batch_vector = `p:real^6`;;
let candle_real_jet_batch_real_lt = `(<):real->real->bool`;;
let candle_real_jet_batch_real_zero = `&0:real`;;

let candle_real_jet_batch_scalar_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_real_jet_batch_scalar_source =
  `&1 * &10 +
   (x1 * x4 * (--x1 + x2 + x3 - x4 + x5 + #4.0) +
    x2 * x5 * (x1 - x2 + x3 + x4 - x5 + #4.0) +
    x3 * #4.0 * (x1 + x2 - x3 + x4 + x5 - #4.0) -
    x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * #4.0 -
    x4 * x5 * #4.0) * -- &1`;;

let candle_real_jet_batch_box_sources =
 [([`&4`; `&4`; `&4`; `&90601 / &10000`; `&4`; `&4`],
   [`&3134400153601 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&3312128000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&90601 / &10000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&6106769920001 / &640000000000`;
    `&1280000000001 / &320000000000`;
    `&2936064000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&6106769920001 / &640000000000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2936064000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&90601 / &10000`; `&4`; `&2936064000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&6106769920001 / &640000000000`;
    `&1280000000001 / &320000000000`;
    `&3312128000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&6106769920001 / &640000000000`; `&4`;
    `&2936064000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&3312128000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`;
    `&2936064000001 / &640000000000`; `&90601 / &10000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&3312128000001 / &640000000000`]);
  ([`&3134400153601 / &640000000000`;
    `&2936064000001 / &640000000000`; `&4`; `&90601 / &10000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&3312128000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&3312128000001 / &640000000000`]);
  ([`&4`; `&4`; `&4`; `&90601 / &10000`; `&4`;
    `&3312128000001 / &640000000000`],
   [`&3134400153601 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&90601 / &10000`; `&4`; `&3312128000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&6106769920001 / &640000000000`;
    `&1280000000001 / &320000000000`;
    `&1844096000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&6106769920001 / &640000000000`; `&4`;
    `&3312128000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&1844096000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&90601 / &10000`; `&4`; `&1844096000001 / &320000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&6106769920001 / &640000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`; `&4`;
    `&6106769920001 / &640000000000`; `&4`;
    `&1844096000001 / &320000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&2936064000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`; `&4`;
    `&2936064000001 / &640000000000`; `&90601 / &10000`; `&4`;
    `&3312128000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&2936064000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&3134400153601 / &640000000000`;
    `&2936064000001 / &640000000000`; `&4`; `&90601 / &10000`; `&4`;
    `&3312128000001 / &640000000000`],
   [`&1854400153601 / &320000000000`;
    `&3312128000001 / &640000000000`;
    `&3312128000001 / &640000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&4`; `&4`; `&3312128000001 / &640000000000`;
    `&90601 / &10000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&3312128000001 / &640000000000`;
    `&2032128000001 / &320000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`]);
  ([`&4`; `&3312128000001 / &640000000000`; `&4`;
    `&90601 / &10000`; `&4`; `&4`],
   [`&1854400153601 / &320000000000`;
    `&2032128000001 / &320000000000`;
    `&2032128000001 / &320000000000`;
    `&3207537920001 / &320000000000`;
    `&1280000000001 / &320000000000`;
    `&2032128000001 / &320000000000`])];;

(* Canonical identities emitted by the authenticated precision-tree capture. *)
let candle_real_jet_batch_expected_box_md5s =
 ["dec2e3d0c4435dd6dd294538f35c9e5f";
  "c81c109787dbeb5e906fbdc09e7a67d9";
  "a158d87b5782fa67d6870cc8b32e18d4";
  "ec215ca401327821f55620c9b7738c22";
  "10515ee9253795b8df17fdcd907e354b";
  "24822df1852519195e848b53969c8e34";
  "94c51c74eade7f99402f24e054306362";
  "9752f62e9e71127bff7bd8e7b12960ab";
  "1e91573442bc2203240b92fb1cf9e24c";
  "4e98b3e058c2ce203ff446aaca3f347c";
  "b66deb6a121378d15491d7c6a64004f2";
  "52a3bf94c9844bf5742322ddeaf9837f";
  "4f45537b8a8092890f8b2aaaec3e5048";
  "48a7b494283dd4b22c57e82090bb87b9";
  "07c3e6f0f99ebc2d6a9b47921a835527";
  "93accb0313cb39cd95d204972088ffde"];;

let candle_real_jet_batch_program_encode_conv program =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_instruction_list`,program));;

let candle_real_jet_batch_boxes_encode_conv boxes =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,boxes));;

let candle_real_jet_batch_marker index phase event =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_BATCH box=" ^ string_of_int index ^
     " phase=" ^ phase ^ " event=" ^ event);;

let rec candle_real_jet_batch_bound_strings bounds =
  match bounds with
  | [] -> []
  | bound :: rest ->
      Num.string_of_num (rat_of_term bound) ::
      candle_real_jet_batch_bound_strings rest;;

let candle_real_jet_batch_box_md5 lower upper =
  Digest.to_hex
    (Digest.string
      (String.concat "," (candle_real_jet_batch_bound_strings lower) ^ "|" ^
       String.concat "," (candle_real_jet_batch_bound_strings upper)));;

let candle_real_jet_batch_compute index phase equations tm =
  candle_real_jet_batch_marker index phase "begin";
  let th = compute equations tm in
  candle_real_jet_batch_marker index phase "end";
  if hyp th <> [] then
    failwith ("shared-jet batch compute assumptions in " ^ phase);
  th;;

let candle_real_jet_batch_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "shared-jet batch final result is not a pair";;

let candle_real_jet_batch_flag_accept = prove
 (`!b. (1:num) = (if b then 1 else 0) ==> b`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let candle_real_jet_batch_suc_one = SYM ONE;;
let candle_real_jet_batch_dim_six = DIMINDEX_CONV `dimindex (:6)`;;
let candle_real_jet_batch_sound_six =
  REWRITE_RULE
    [candle_real_jet_batch_dim_six]
    (INST_TYPE
      [`:6`,`:N`]
      candle_q_dim_poly_jet_whole_box_accept_sound);;

let _ =
  print_endline
    "CANDLE_CV_REAL_FLYSPECK_JET_BATCH box=all phase=source-reify event=begin";;

let candle_real_jet_batch_first_lower,
    candle_real_jet_batch_first_upper =
  hd candle_real_jet_batch_box_sources;;

let candle_real_jet_batch_source,
    candle_real_jet_batch_first_boxes,
    candle_real_jet_batch_expression,
    candle_real_jet_batch_valid,
    candle_real_jet_batch_source_th,
    candle_real_jet_batch_program,
    candle_real_jet_batch_run_th =
  candle_poly_prepare_scalar_fixture
    candle_real_jet_batch_vector
    candle_real_jet_batch_scalar_variables
    candle_real_jet_batch_scalar_source
    candle_real_jet_batch_first_lower
    candle_real_jet_batch_first_upper;;

let candle_real_jet_batch_compile_th =
  REWRITE_CONV [candle_poly_compile_def; APPEND]
    (mk_comb (`candle_poly_compile`,candle_real_jet_batch_expression));;

if not
    (aconv (rand (concl candle_real_jet_batch_compile_th))
           candle_real_jet_batch_program) then
  failwith "shared-jet batch compiler/reifier program mismatch";;

let candle_real_jet_batch_program_rep =
  candle_real_jet_batch_program_encode_conv candle_real_jet_batch_program;;

let candle_real_jet_batch_program_rep_tm =
  rand (concl candle_real_jet_batch_program_rep);;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_BATCH box=all phase=source-reify event=end " ^
     "instructions=" ^
     string_of_int (length (dest_list candle_real_jet_batch_program)));;

let candle_real_jet_batch_check_box index (lower,upper) =
  let box_md5 = candle_real_jet_batch_box_md5 lower upper in
  if box_md5 <> List.nth candle_real_jet_batch_expected_box_md5s index then
    failwith "shared-jet batch captured box identity mismatch";
  candle_real_jet_batch_marker index "box-prepare" "begin";
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_rep = candle_real_jet_batch_boxes_encode_conv boxes in
  let boxes_rep_tm = rand (concl boxes_rep) in
  candle_real_jet_batch_marker index "box-prepare" "end";

  let center_environment_th =
    candle_real_jet_batch_compute index "center-environment"
      candle_cv_q_dim_first_jet_compute_eqs
      (mk_comb
        (`candle_cv_q_center_environment_list`,boxes_rep_tm)) in
  let center_environment = rand (concl center_environment_th) in

  let center_th =
    candle_real_jet_batch_compute index "center-first-jet"
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_first_jet_program`,
         [center_environment;candle_real_jet_batch_program_rep_tm])) in
  let center = rand (concl center_th) in

  let box_th =
    candle_real_jet_batch_compute index "box-second-jet"
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_jet_program`,
         [boxes_rep_tm;candle_real_jet_batch_program_rep_tm])) in
  let box = rand (concl box_th) in

  let upper_th =
    candle_real_jet_batch_compute index "taylor-handoff"
      (candle_cv_q_dim_first_jet_compute_eqs @
       [SPEC_ALL candle_cv_q_jet_upper_pair_def])
      (list_mk_comb
        (`candle_cv_q_jet_upper_pair`,
         [boxes_rep_tm;center;box])) in
  let upper = rand (concl upper_th) in

  let valid_th =
    candle_real_jet_batch_compute index "box-valid"
      candle_cv_q_dim_first_jet_compute_eqs
      (mk_comb (`candle_cv_q_box_valid_list`,boxes_rep_tm)) in
  let valid = rand (concl valid_th) in

  let finish_th =
    candle_real_jet_batch_compute index "finish"
      candle_cv_q_dim_first_jet_compute_eqs
      (list_mk_comb
        (`candle_cv_q_dim_whole_box_finish`,
         [`Cexp_num 1`;valid;upper])) in
  let finish = rand (concl finish_th) in
  let verdict,_ = candle_real_jet_batch_dest_pair finish in
  if not (aconv verdict `Cexp_num 1`) then
    failwith ("shared-jet batch box " ^ string_of_int index ^ " rejected");

  candle_real_jet_batch_marker index "theorem-handoff" "begin";
  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_poly_jet_whole_box_check`,
       [candle_real_jet_batch_program_rep_tm;boxes_rep_tm]) in
  let expansion_th =
    REWRITE_CONV
      [candle_cv_q_dim_poly_jet_whole_box_check_def;
       candle_cv_q_dim_poly_jet_whole_box_upper_def]
      compute_tm in
  let evaluation_th =
    REWRITE_CONV
      [center_environment_th;center_th;box_th;upper_th;valid_th;finish_th]
      (rand (concl expansion_th)) in
  let compute_th = TRANS expansion_th evaluation_th in
  let correctness =
    SPECL
      [candle_real_jet_batch_expression;boxes]
      candle_cv_q_dim_poly_jet_whole_box_check_correct in
  let abstract_compute_th =
    let th =
      PURE_REWRITE_RULE
        [SYM candle_real_jet_batch_program_rep;SYM boxes_rep]
        compute_th in
    PURE_REWRITE_RULE [SYM candle_real_jet_batch_compile_th] th in
  if not
      (aconv (lhand (concl abstract_compute_th))
             (lhand (concl correctness))) then
    failwith "shared-jet batch abstract/concrete checker lhs mismatch";
  let accept_encoding_th = TRANS (SYM abstract_compute_th) correctness in
  let numerical_goal =
    list_mk_comb
      (`candle_q_dim_poly_jet_whole_box_numerical_accept`,
       [candle_real_jet_batch_expression;boxes]) in
  let abstract_verdict_th =
    PURE_REWRITE_RULE [candle_real_jet_batch_suc_one]
      (REWRITE_RULE [cexp_fst_def]
        (AP_TERM `Cexp_fst` accept_encoding_th)) in
  let computed_verdict_th =
    REWRITE_RULE [cexp_fst_def]
      (AP_TERM `Cexp_fst` finish_th) in
  if not
      (aconv (lhand (concl computed_verdict_th))
             (lhand (concl abstract_verdict_th))) then
    failwith "shared-jet batch computed/abstract verdict lhs mismatch";
  let verdict_th = TRANS (SYM computed_verdict_th) abstract_verdict_th in
  let flag_num_th = REWRITE_RULE [injectivity "cval"] verdict_th in
  let expected_flag =
    mk_eq (`1`,mk_cond (numerical_goal,`1`,`0`)) in
  let flag_num_th =
    if aconv (concl flag_num_th) expected_flag then flag_num_th
    else if aconv (concl flag_num_th)
              (mk_eq (rand expected_flag,lhand expected_flag)) then
      SYM flag_num_th
    else failwith "shared-jet batch numerical flag theorem mismatch" in
  let numerical_th =
    MATCH_MP
      (SPEC numerical_goal candle_real_jet_batch_flag_accept)
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
        candle_real_jet_batch_sound_six)
      (CONJ candle_real_jet_batch_valid
        (CONJ length_six numerical_th)) in
  let source_th =
    REWRITE_RULE [candle_real_jet_batch_source_th] vector_th in
  let p,body = dest_forall (concl source_th) in
  let _,claim = dest_imp body in
  let partial,zero = dest_comb claim in
  let relation,source = dest_comb partial in
  if hyp compute_th <> [] || hyp numerical_th <> [] ||
     hyp vector_th <> [] || hyp source_th <> [] ||
     not (aconv p candle_real_jet_batch_vector) ||
     not (aconv relation candle_real_jet_batch_real_lt) ||
     not (aconv source candle_real_jet_batch_source) ||
     not (aconv zero candle_real_jet_batch_real_zero) then
    failwith "shared-jet batch source theorem mismatch";
  candle_real_jet_batch_marker index "theorem-handoff" "end";
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_JET_BATCH_RESULT box=" ^
     string_of_int index ^ " verdict=accept box_md5=" ^ box_md5 ^
     " theorem_md5=" ^
     Digest.to_hex (Digest.string (string_of_thm source_th)));
  source_th;;

let candle_real_jet_batch_theorems =
  map2 candle_real_jet_batch_check_box
    (0--15) candle_real_jet_batch_box_sources;;

if length candle_real_jet_batch_theorems <> 16 ||
   hyp candle_real_jet_batch_valid <> [] ||
   hyp candle_real_jet_batch_source_th <> [] ||
   hyp candle_real_jet_batch_run_th <> [] then
  failwith "shared-jet batch result count or source assumptions drift";;

let _ =
  print_endline
    "CANDLE_CV_REAL_FLYSPECK_JET_BATCH_STATS programs=1 boxes=16 accepted=16";;

let _ = print_endline "CANDLE_CV_REAL_FLYSPECK_JET_BATCH_OK";;

end;;
