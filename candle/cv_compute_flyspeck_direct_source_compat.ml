(* ========================================================================== *)
(* Direct-source reconstruction for reflected Flyspeck nonlinear fixtures.    *)
(*                                                                            *)
(* Historical experimental checkpoints exposed generated [Definitions] and   *)
(* [Break_case] modules.  The direct Flyspeck path authenticates the split    *)
(* source modules below.  Keep that name-resolution adaptation in one place   *)
(* while retaining the original conversion and rewrite intent.                *)
(* ========================================================================== *)

module Candle_cv_flyspeck_direct_source_compat = struct

(* The complete [Break_case_exec] module performs the historical nonlinear
   replay as a top-level effect.  The reflected source fixture needs only the
   following five rewrite theorems.  Prove that exact interface directly from
   the same authenticated Flyspeck definitions, using the original proof
   scripts, so loading the fast checker does not repeat the legacy replay. *)
let candle_direct_subat_rules = prove_by_refinement(
  `(!i (y:A). subat i y [] = []) /\
    (!x xs (y:A). subat 0 y (x::xs) = y :: xs) /\
    (!i x xs (y:A). subat (SUC i) y (x::xs) = x :: (subat i) y xs)`,
  [
  ONCE_REWRITE_TAC[Sphere.subat];
  Hales_tactic.BY
    (REWRITE_TAC
      [Hales_tactic.arith `~(SUC i = 0)`;
       Hales_tactic.arith `SUC i - 1 = i`])
  ]);;

let candle_direct_subat_explicit = prove_by_refinement(
  `(!i x xs (y:A).
      subat 9 y (x::xs) = x :: (subat 8 y xs) /\
      subat 8 y (x::xs) = x :: (subat 7 y xs) /\
      subat 7 y (x::xs) = x :: (subat 6 y xs) /\
      subat 6 y (x::xs) = x :: (subat 5 y xs) /\
      subat 5 y (x::xs) = x :: (subat 4 y xs) /\
      subat 4 y (x::xs) = x :: (subat 3 y xs) /\
      subat 3 y (x::xs) = x :: (subat 2 y xs) /\
      subat 2 y (x::xs) = x :: (subat 1 y xs) /\
      subat 1 y (x::xs) = x :: (subat 0 y xs) /\
      subat 0 y (x::xs) = y :: xs)`,
  [
  Hales_tactic.BY(REWRITE_TAC
    [Hales_tactic.arith
      `9 = SUC 8 /\ 8 = SUC 7 /\ 7 = SUC 6 /\ 6 = SUC 5 /\
       5 = SUC 4 /\ 4 = SUC 3 /\ 3 = SUC 2 /\ 2 = SUC 1 /\ 1 = SUC 0`;
     candle_direct_subat_rules])
  ]);;

let candle_direct_bisect_left_frac = prove_by_refinement(
  `!d i. bisect_left i d = frac_left i (#0.5) d`,
  [
  REWRITE_TAC
    [Sphere.bisect_left;Sphere.frac_left;Hales_tactic.LET_THM];
  LIST_INDUCT_TAC THEN REWRITE_TAC[Sphere.subat;LAMBDA_PAIR];
  REPEAT Hales_tactic.WEAKER_STRIP_TAC;
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EL;HD;TL;Sphere.pathL;CONS_11];
    Hales_tactic.INTRO_TAC PAIR_SURJECTIVE [`h`] THEN
      REPEAT Hales_tactic.WEAKER_STRIP_TAC THEN
      ASM_REWRITE_TAC[Sphere.pathL;PAIR_EQ];
    Hales_tactic.BY(ARITH_TAC);
  Hales_tactic.INTRO_TAC num_CASES [`i`];
  ASM_REWRITE_TAC[] THEN REPEAT Hales_tactic.WEAKER_STRIP_TAC THEN
    ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[EL;TL];
  Hales_tactic.BY
    (ASM_REWRITE_TAC
      [EL;TL;Hales_tactic.arith `SUC n - 1 = n`;LAMBDA_PAIR])
  ]);;

let candle_direct_bisect_right_frac = prove_by_refinement(
  `!d i. bisect_right i d = frac_right i (#0.5) d`,
  [
  REWRITE_TAC
    [Sphere.bisect_right;Sphere.frac_right;Hales_tactic.LET_THM];
  LIST_INDUCT_TAC THEN REWRITE_TAC[Sphere.subat;LAMBDA_PAIR];
  REPEAT Hales_tactic.WEAKER_STRIP_TAC;
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EL;HD;TL;Sphere.pathR;CONS_11];
    Hales_tactic.INTRO_TAC PAIR_SURJECTIVE [`h`] THEN
      REPEAT Hales_tactic.WEAKER_STRIP_TAC THEN
      ASM_REWRITE_TAC[Sphere.pathR;PAIR_EQ];
    Hales_tactic.BY(ARITH_TAC);
  Hales_tactic.INTRO_TAC num_CASES [`i`];
  ASM_REWRITE_TAC[] THEN REPEAT Hales_tactic.WEAKER_STRIP_TAC THEN
    ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[EL;TL];
  Hales_tactic.BY
    (ASM_REWRITE_TAC
      [EL;TL;Hales_tactic.arith `SUC n - 1 = n`;LAMBDA_PAIR])
  ]);;

let candle_direct_ineq6m = prove_by_refinement(
  `!x1 x2 x3 x4 x5 x6 a1 a2 a3 a4 a5 a6 b1 b2 b3 b4 b5 b6 f.
    ineqm [x1;x2;x3;x4;x5;x6]
      [(a1,b1);(a2,b2);(a3,b3);(a4,b4);(a5,b5);(a6,b6)] f =
    ineq
      [(a1,x1,b1);(a2,x2,b2);(a3,x3,b3);(a4,x4,b4);(a5,x5,b5);
       (a6,x6,b6)] f`,
  [
  REWRITE_TAC[Sphere.ineqm];
  Hales_tactic.BY(REWRITE_TAC[MAP2])
  ]);;

let candle_direct_ineq9m = prove_by_refinement(
  `!x1 x2 x3 x4 x5 x6 x7 x8 x9
    a1 a2 a3 a4 a5 a6 a7 a8 a9 b1 b2 b3 b4 b5 b6 b7 b8 b9 f.
    ineqm [x1;x2;x3;x4;x5;x6;x7;x8;x9]
      [(a1,b1);(a2,b2);(a3,b3);(a4,b4);(a5,b5);(a6,b6);
       (a7,b7);(a8,b8);(a9,b9)] f =
    ineq
      [(a1,x1,b1);(a2,x2,b2);(a3,x3,b3);(a4,x4,b4);(a5,x5,b5);
       (a6,x6,b6);(a7,x7,b7);(a8,x8,b8);(a9,x9,b9)] f`,
  [
  REWRITE_TAC[Sphere.ineqm];
  Hales_tactic.BY(REWRITE_TAC[MAP2])
  ]);;

(* The generated closure used [Break_case.ineqm_conv], whose rational
   reduction is deliberately confined to the domain-list reconstruction.
   [Break_case_exec.ineq_conv] is not equivalent here: it applies
   [REAL_RAT_REDUCE_CONV] to the whole inequality and expands decimal
   coefficient products in the function body.  Reproduce the original
   conversion boundary using the corresponding authenticated direct-source
   theorems. *)
let rec candle_direct_ineqm_conv =
  let domain_conv =
    REWRITE_CONV
      [Sphere.frac_left;
       Sphere.frac_right;
       candle_direct_bisect_left_frac;
       candle_direct_bisect_right_frac;
       candle_direct_subat_explicit;
       Hales_tactic.LET_THM;
       LAMBDA_PAIR;
       Basics.EL_EXPLICIT]
    THENC REAL_RAT_REDUCE_CONV in
  fun tm ->
    try
      let list_path = find_path is_list tm in
      if String.length list_path <= 2 then
        REWRITE_CONV
          [candle_direct_ineq6m; candle_direct_ineq9m] tm
      else
        let parent_path =
          String.sub list_path 0 (String.length list_path - 1) in
        (PATH_CONV parent_path domain_conv THENC candle_direct_ineqm_conv) tm
    with Failure _ ->
      ALL_CONV tm;;

let candle_direct_flyspeck_defs =
  [Sphere.delta_x;
   Sphere.delta_x4;
   Sphere.delta4_squared_x;
   Sphere.x1_delta_x;
   Nonlinear_lemma.unit6;
   Nonlinear_lemma.rho_alt;
   Nonlinear_lemma.sqrt_x1;
   Nonlinear_lemma.sqrt_x2;
   Nonlinear_lemma.sqrt_x3;
   Nonlinear_lemma.sqrt_x4;
   Nonlinear_lemma.sqrt_x5;
   Nonlinear_lemma.sqrt_x6;
   Sphere.dihatn_x;
   Sphere.dih2atn_x;
   Sphere.dih3atn_x;
   Sphere.rhazimatn_x;
   Sphere.rhazim2atn_x;
   Sphere.rhazim3atn_x;
   Sphere.sol0;
   GSYM Nonlinear_lemma.sol0_over_pi_EQ_const1;
   Sphere.rotate2;
   Sphere.rotate3;
   REAL_POW_2];;

let candle_direct_expand_ineq_case =
  REWRITE_CONV
    [Sphere.ineq; IMP_IMP; REAL_MUL_LZERO; REAL_MUL_RZERO]
  THENC REWRITE_CONV candle_direct_flyspeck_defs
  THENC DEPTH_CONV let_CONV;;

(* [M_verifier_main.exprs_to_vector_fun] uses OCaml polymorphic ordering to
   sort HOL terms.  Candle deliberately rejects that untyped operation.  The
   kernel's total term order is the corresponding explicit order already used
   by the direct-source compatibility normalizations. *)
let candle_direct_exprs_to_vector_fun expr_tms =
  let comp_op = `$` in
  let vars = List.sort Term.compare (unions (map frees expr_tms)) in
  let n = length vars in
  let x_var =
    mk_var ("x",M_taylor.n_vector_type_array.(if n = 0 then 1 else n)) in
  let x_tm = mk_icomb (comp_op,x_var) in
  let vars2 =
    map (fun i -> mk_comb (x_tm,mk_small_numeral i)) (1--n) in
  map (fun tm -> mk_abs (x_var,subst (zip vars2 vars) tm)) expr_tms,
  (if n = 0 then M_taylor.mk_vector_list [x_var]
   else M_taylor.mk_vector_list vars);;

end;;
