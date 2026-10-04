(* ========================================================================== *)
(* Direct-source reconstruction for reflected Flyspeck nonlinear fixtures.    *)
(*                                                                            *)
(* Historical experimental checkpoints exposed generated [Definitions] and   *)
(* [Break_case] modules.  The direct Flyspeck path authenticates the split    *)
(* source modules below.  Keep that name-resolution adaptation in one place   *)
(* while retaining the original conversion and rewrite intent.                *)
(* ========================================================================== *)

module Candle_cv_flyspeck_direct_source_compat = struct

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
       Break_case_exec.bisect_left_frac;
       Break_case_exec.bisect_right_frac;
       Break_case_exec.subat_explicit;
       Hales_tactic.LET_THM;
       LAMBDA_PAIR;
       Basics.EL_EXPLICIT]
    THENC REAL_RAT_REDUCE_CONV in
  fun tm ->
    try
      let list_path = find_path is_list tm in
      if String.length list_path <= 2 then
        REWRITE_CONV
          [Break_case_exec.ineq6m; Break_case_exec.ineq9m] tm
      else
        let parent_path =
          String.sub list_path 0 (String.length list_path - 1) in
        (PATH_CONV parent_path domain_conv THENC candle_direct_ineqm_conv) tm
    with Failure _ ->
      ALL_CONV tm;;

let candle_direct_flyspeck_defs =
  [Nonlinear_lemma.unit6;
   Nonlinear_lemma.sqrt_x1;
   Nonlinear_lemma.sqrt_x2;
   Nonlinear_lemma.sqrt_x3;
   Nonlinear_lemma.sqrt_x4;
   Nonlinear_lemma.sqrt_x5;
   Nonlinear_lemma.sqrt_x6;
   Sphere.dihatn_x;
   Sphere.delta_x4;
   Sphere.delta_x];;

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
