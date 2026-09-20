(* ========================================================================== *)
(* Kernel-authenticated polynomial recentering for exact interval programs.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  ML chooses fresh offset variables and asks    *)
(* REAL_POLY_CONV for a centered polynomial, but the selected program is      *)
(* authorized only by a kernel theorem equating it to the original source    *)
(* expression.  This preserves the public theorem expression while reducing  *)
(* interval dependency loss.                                                 *)
(* ========================================================================== *)

needs "candle/cv_compute_exact_interval_reify.ml";;

module Candle_cv_exact_interval_recenter = struct

open Candle_cv_exact_interval_program;;
open Candle_cv_exact_interval_reify;;

let candle_q_real_add = `(+):real->real->real`;;
let candle_q_real_sub = `(-):real->real->real`;;

let candle_q_recenter_expression variables centers tm =
  if length variables <> length centers then
    failwith "candle_q recenter: variable/center length mismatch";
  if exists (fun variable -> type_of variable <> `:real`) variables then
    failwith "candle_q recenter: non-real variable basis";
  if exists (fun center -> type_of center <> `:real` || not (is_ratconst center))
       centers then
    failwith "candle_q recenter: center is not an exact real rational";
  if type_of tm <> `:real` then
    failwith "candle_q recenter: expression is not real";
  let abstract_offsets = map (fun _ -> genvar `:real`) variables in
  let shifted_values =
    map2
      (fun center offset -> mk_binop candle_q_real_add center offset)
      centers abstract_offsets in
  let shifted = vsubst (zip shifted_values variables) tm in
  let normalization_th = REAL_POLY_CONV shifted in
  let normalized_abstract = rand (concl normalization_th) in
  let concrete_offsets =
    map2
      (fun variable center -> mk_binop candle_q_real_sub variable center)
      variables centers in
  let normalized =
    vsubst (zip concrete_offsets abstract_offsets) normalized_abstract in
  let source_eq = prove
    (mk_eq (tm,normalized),
     CONV_TAC REAL_RING) in
  if hyp source_eq <> [] || not (aconv (lhand (concl source_eq)) tm) then
    failwith "candle_q recenter: kernel normalization mismatch";
  concrete_offsets,normalized,source_eq;;

let candle_q_reify_recentered_real_expression variables centers tm =
  let offsets,normalized,source_eq =
    candle_q_recenter_expression variables centers tm in
  let program,normalized_run_th =
    candle_q_reify_real_expression offsets normalized in
  let source_run_th = REWRITE_RULE[SYM source_eq] normalized_run_th in
  let expected =
    mk_eq
      (list_mk_comb
        (`candle_q_real_run`,
         [mk_list (offsets,`:real`);program;`[]:real list`]),
       mk_list ([tm],`:real`)) in
  if hyp source_run_th <> [] || not (aconv (concl source_run_th) expected) then
    failwith "candle_q recenter: source execution theorem mismatch";
  offsets,normalized,source_eq,program,source_run_th;;

let candle_q_prove_recentered_interval_expression
      variables centers intervals_tm environment_contains_th tm =
  let offsets,normalized,source_eq,program,source_run_th =
    candle_q_reify_recentered_real_expression variables centers tm in
  let _,_,result_intervals,_,compute_th,ordinary_result_th =
    candle_q_compute_interval_program
      offsets intervals_tm tm program source_run_th in
  let empty_intervals = mk_list ([],candle_q_interval_type) in
  let empty_reals = `[]:real list` in
  let empty_contains_th =
    EQT_ELIM
      (REWRITE_CONV[candle_q_stack_contains_def]
        `candle_q_stack_contains
           ([]:(((num#num)#num)#((num#num)#num))list) ([]:real list)`) in
  let sound_th =
    SPECL
      [program;intervals_tm;mk_list (offsets,`:real`);
       empty_intervals;empty_reals]
      candle_q_interval_run_sound in
  let sound_th =
    MP sound_th (CONJ environment_contains_th empty_contains_th) in
  let sound_th =
    REWRITE_RULE
      [ordinary_result_th;source_run_th;candle_q_stack_contains_def]
      sound_th in
  let result_interval = hd (dest_list result_intervals) in
  let expected =
    list_mk_comb (`candle_q_interval_contains`,[result_interval;tm]) in
  if not (aconv (concl sound_th) expected) then
    failwith "candle_q recenter: final interval theorem mismatch";
  offsets,normalized,source_eq,result_interval,program,compute_th,sound_th;;

end;;
