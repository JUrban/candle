(* ========================================================================== *)
(* Flyspeck instantiation of the exact linear-function reifier.               *)
(*                                                                            *)
(* Load only after Flyspeck's lin_f, Arith_num, and Arith_int modules. The   *)
(* generic reifier remains responsible for constructing a kernel equality;    *)
(* these wrappers select the exact source representation used by the checker. *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_reify.ml";;
needs "candle/cv_compute_linear_combination_adapter.ml";;

module Candle_cv_linear_combination_flyspeck = struct

open Candle_cv_linear_combination_reify;;
open Candle_cv_linear_combination_adapter;;

let candle_lc_flyspeck_zero = num 0;;

let candle_lc_flyspeck_lin_f_const = `lin_f`;;
let candle_lc_flyspeck_rewrites = [];;

(* Real LP masters repeat a very small vocabulary of Flyspeck numeral terms
   across many otherwise distinct [lin_f] rows.  NUM_TO_NUMERAL_CONV is
   proof-producing, so cache only its successful exact input theorems and
   recheck every hit before DEPTH_CONV uses it.  Keep the cache bounded; it is
   an edit/runtime optimization and never proof authority. *)
let candle_lc_flyspeck_numeral_cache : (term,thm) Hashtbl.t =
  Hashtbl.create 257;;
let candle_lc_flyspeck_numeral_cache_hits = ref 0;;
let candle_lc_flyspeck_numeral_cache_misses = ref 0;;

let candle_lc_flyspeck_clear_numeral_cache () =
  Hashtbl.clear candle_lc_flyspeck_numeral_cache;
  candle_lc_flyspeck_numeral_cache_hits := 0;
  candle_lc_flyspeck_numeral_cache_misses := 0;;

let candle_lc_flyspeck_numeral_cache_stats () =
  !candle_lc_flyspeck_numeral_cache_hits,
  !candle_lc_flyspeck_numeral_cache_misses,
  Hashtbl.length candle_lc_flyspeck_numeral_cache;;

let candle_lc_flyspeck_cached_numeral_conv tm =
  try
    let th = Hashtbl.find candle_lc_flyspeck_numeral_cache tm in
    if hyp th <> [] || not (aconv (lhand (concl th)) tm) then
      failwith "Flyspeck numeral cache theorem mismatch";
    candle_lc_flyspeck_numeral_cache_hits :=
      !candle_lc_flyspeck_numeral_cache_hits + 1;
    th
  with Not_found ->
    let th = Arith_nat.NUM_TO_NUMERAL_CONV tm in
    if hyp th <> [] || not (aconv (lhand (concl th)) tm) then
      failwith "Flyspeck numeral conversion theorem mismatch";
    if Hashtbl.length candle_lc_flyspeck_numeral_cache >= 4096 then
      Hashtbl.clear candle_lc_flyspeck_numeral_cache;
    Hashtbl.add candle_lc_flyspeck_numeral_cache tm th;
    candle_lc_flyspeck_numeral_cache_misses :=
      !candle_lc_flyspeck_numeral_cache_misses + 1;
    th;;

let candle_lc_flyspeck_standardize_numerals tm =
  DEPTH_CONV candle_lc_flyspeck_cached_numeral_conv tm;;

let candle_lc_reify_flyspeck_lin_f variables lhs =
  let standardize_th = candle_lc_flyspeck_standardize_numerals lhs in
  let standard_lhs = rand (concl standardize_th) in
  let coefficients,standard_th =
    candle_lc_reify_lin_f_with
      Term.(<)
      candle_lc_flyspeck_lin_f_const
      Linear_function.lin_f
      dest_realintconst
      candle_lc_flyspeck_rewrites
      variables standard_lhs in
  coefficients,TRANS standard_th (SYM standardize_th);;

let candle_lc_reify_flyspeck_integer integer_tm =
  let standardize_th =
    candle_lc_flyspeck_standardize_numerals integer_tm in
  let standard_integer = rand (concl standardize_th) in
  let integer,standard_th =
    candle_lc_reify_integer_with
      Linear_function.lin_f
      dest_realintconst
      candle_lc_flyspeck_rewrites
      standard_integer in
  integer,TRANS standard_th (SYM standardize_th);;

(* Reification equalities depend on the exact variable basis and source term,
   but not on a terminal's certificate multiplier.  Retain only the current
   basis so preparation is reusable within one certificate family without an
   unbounded cross-corpus theorem cache.  Every cache hit is still checked
   against its exact requested conclusion before use. *)
let candle_lc_reification_cache_basis : term option ref = ref None;;
let candle_lc_lhs_reification_cache :
    (term,term * thm) Hashtbl.t = Hashtbl.create 1021;;
let candle_lc_rhs_reification_cache :
    (term,term * thm) Hashtbl.t = Hashtbl.create 1021;;
let candle_lc_lhs_cache_hits = ref 0 and
    candle_lc_lhs_cache_misses = ref 0 and
    candle_lc_rhs_cache_hits = ref 0 and
    candle_lc_rhs_cache_misses = ref 0;;

let candle_lc_clear_reification_cache () =
  candle_lc_reification_cache_basis := None;
  Hashtbl.clear candle_lc_lhs_reification_cache;
  Hashtbl.clear candle_lc_rhs_reification_cache;;

let candle_lc_reset_reification_cache_stats () =
  candle_lc_lhs_cache_hits := 0;
  candle_lc_lhs_cache_misses := 0;
  candle_lc_rhs_cache_hits := 0;
  candle_lc_rhs_cache_misses := 0;;

let candle_lc_reification_cache_stats () =
  (!candle_lc_lhs_cache_hits,!candle_lc_lhs_cache_misses,
   !candle_lc_rhs_cache_hits,!candle_lc_rhs_cache_misses,
   Hashtbl.length candle_lc_lhs_reification_cache,
   Hashtbl.length candle_lc_rhs_reification_cache);;

let candle_lc_prepare_reification_cache variables =
  let variables_tm = mk_list (variables,`:real`) in
  match !candle_lc_reification_cache_basis with
  | Some cached when cached = variables_tm -> variables_tm
  | _ ->
      candle_lc_reification_cache_basis := Some variables_tm;
      Hashtbl.clear candle_lc_lhs_reification_cache;
      Hashtbl.clear candle_lc_rhs_reification_cache;
      variables_tm;;

let candle_lc_reify_flyspeck_lin_f_cached variables variables_tm lhs =
  try
      let coefficients,lhs_th =
        Hashtbl.find candle_lc_lhs_reification_cache lhs in
      let expected_lhs =
        mk_comb
          (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients) in
      candle_lc_check_reification "cached lhs" expected_lhs lhs lhs_th;
      candle_lc_lhs_cache_hits := !candle_lc_lhs_cache_hits + 1;
      coefficients,lhs_th
  with Not_found ->
      let result = candle_lc_reify_flyspeck_lin_f variables lhs in
      Hashtbl.replace candle_lc_lhs_reification_cache lhs result;
      candle_lc_lhs_cache_misses := !candle_lc_lhs_cache_misses + 1;
      result;;

let candle_lc_reify_flyspeck_integer_cached integer_tm =
  try
      let integer,rhs_th =
        Hashtbl.find candle_lc_rhs_reification_cache integer_tm in
      let expected_rhs = mk_comb (`candle_lc_zreal`,integer) in
      candle_lc_check_reification
        "cached rhs" expected_rhs integer_tm rhs_th;
      candle_lc_rhs_cache_hits := !candle_lc_rhs_cache_hits + 1;
      integer,rhs_th
  with Not_found ->
      let result = candle_lc_reify_flyspeck_integer integer_tm in
      Hashtbl.replace candle_lc_rhs_reification_cache integer_tm result;
      candle_lc_rhs_cache_misses := !candle_lc_rhs_cache_misses + 1;
      result;;

let candle_lc_dest_canonical_z z_tm =
  let positive_tm,negative_tm = dest_pair z_tm in
  let positive = dest_numeral positive_tm and
      negative = dest_numeral negative_tm in
  if positive =/ candle_lc_flyspeck_zero then minus_num negative
  else if negative =/ candle_lc_flyspeck_zero then positive
  else failwith "Flyspeck adapter: noncanonical signed pair";;

let candle_lc_render_flyspeck_z z_tm =
  Arith_int.my_mk_realintconst (candle_lc_dest_canonical_z z_tm);;

let candle_lc_render_flyspeck_lin_f variables coefficients_tm =
  let coefficients = dest_list coefficients_tm in
  let rec render_entries vars coeffs =
    match vars,coeffs with
    | [],[] -> []
    | variable::vars_tail,coefficient::coeffs_tail ->
        let rest = render_entries vars_tail coeffs_tail in
        let integer = candle_lc_dest_canonical_z coefficient in
        if integer =/ candle_lc_flyspeck_zero then rest
        else mk_pair (Arith_int.my_mk_realintconst integer,variable) :: rest
    | _ -> failwith "Flyspeck adapter: coefficient/basis length mismatch" in
  let entries = render_entries variables coefficients in
  mk_comb
    (candle_lc_flyspeck_lin_f_const,mk_list (entries,`:real#real`));;

let candle_lc_publicize_flyspeck variables result exact_th =
  let variables_tm = mk_list (variables,`:real`) in
  let coefficients,integer = dest_pair result in
  let public_lhs =
    candle_lc_render_flyspeck_lin_f variables coefficients in
  let public_rhs = candle_lc_render_flyspeck_z integer in
  let checked_coefficients,lhs_th =
    candle_lc_reify_flyspeck_lin_f variables public_lhs in
  let checked_integer,rhs_th =
    candle_lc_reify_flyspeck_integer public_rhs in
  if not (aconv checked_coefficients coefficients) ||
     not (aconv checked_integer integer) then
    failwith "Flyspeck adapter: public rendering did not reify exactly";
  let expected_exact =
    mk_binop `(<=):real->real->bool`
      (mk_comb
        (mk_comb (`candle_lc_vec_real`,variables_tm),coefficients))
      (mk_comb (`candle_lc_zreal`,integer)) in
  if not (aconv (concl exact_th) expected_exact) then
    failwith "Flyspeck adapter: exact conclusion mismatch";
  let public_eq =
    MK_COMB (AP_TERM `(<=):real->real->bool` lhs_th,rhs_th) in
  let public_th = EQ_MP public_eq exact_th in
  let expected_public =
    mk_binop `(<=):real->real->bool` public_lhs public_rhs in
  if not (aconv (concl public_th) expected_public) then
    failwith "Flyspeck adapter: public conclusion mismatch";
  public_th;;

let candle_lc_bulk_compute_flyspeck_profiled
      profile variables weighted_inequalities =
  let variables_tm = candle_lc_prepare_reification_cache variables in
  let result,exact_th =
    candle_lc_bulk_compute_with_profile profile
      variables
      (candle_lc_reify_flyspeck_lin_f_cached variables variables_tm)
      candle_lc_reify_flyspeck_integer_cached
      weighted_inequalities in
  profile "theorem-publication" "begin";
  let public_th =
    candle_lc_publicize_flyspeck variables result exact_th in
  profile "theorem-publication" "end";
  result,public_th;;

let candle_lc_bulk_compute_flyspeck variables weighted_inequalities =
  candle_lc_bulk_compute_flyspeck_profiled
    (fun _ _ -> ()) variables weighted_inequalities;;

let candle_lc_normalize_flyspeck_inequality normalize_lhs inequality =
  let lhs,rhs =
    dest_binop `(<=):real->real->bool` (concl inequality) in
  let lhs_th = normalize_lhs lhs in
  let normalized_source,_ = dest_eq (concl lhs_th) in
  if hyp lhs_th <> [] || normalized_source <> lhs then
    failwith "Flyspeck adapter: invalid lhs normalization theorem";
  let normalized =
    EQ_MP
      (AP_THM (AP_TERM `(<=):real->real->bool` lhs_th) rhs)
      inequality in
  if not (set_eq (hyp normalized) (hyp inequality)) then
    failwith "Flyspeck adapter: normalization changed hypotheses";
  normalized;;

let candle_lc_flyspeck_lhs_variables inequality =
  let lhs,_ = dest_binop `(<=):real->real->bool` (concl inequality) in
  let head,entries_tm = dest_comb lhs in
  if head <> candle_lc_flyspeck_lin_f_const then
    failwith "Flyspeck adapter: normalized lhs is not lin_f";
  map (fun entry -> snd (dest_pair entry)) (dest_list entries_tm);;

let candle_lc_bulk_compute_flyspeck_source_profiled
      profile normalize_lhs weighted_inequalities =
  profile "source-normalization-variable-discovery" "begin";
  let normalized =
    map
      (fun (inequality,weight) ->
         candle_lc_normalize_flyspeck_inequality
           normalize_lhs inequality,weight)
      weighted_inequalities in
  let variables =
    setify Term.(<)
      (List.flatten
        (map
          (fun (inequality,_) ->
             candle_lc_flyspeck_lhs_variables inequality)
          normalized)) in
  profile "source-normalization-variable-discovery" "end";
  let result,computed_th =
    candle_lc_bulk_compute_flyspeck_profiled
      profile variables normalized in
  variables,result,computed_th;;

let candle_lc_bulk_compute_flyspeck_source
      normalize_lhs weighted_inequalities =
  candle_lc_bulk_compute_flyspeck_source_profiled
    (fun _ _ -> ()) normalize_lhs weighted_inequalities;;

let candle_lc_flyspeck_final_inequality =
  Arith_nat.NUMERALS_TO_NUM
    (prove
      (`!n. lin_f [] <= -- &n <=> n = 0`,
       REWRITE_TAC
         [Linear_function.LIN_F_EMPTY; REAL_NEG_GE0; REAL_OF_NUM_LE; LE]));;

let candle_lc_all_zero_coefficients coefficients_tm =
  List.for_all
    (fun coefficient_tm ->
       let positive_tm,negative_tm = dest_pair coefficient_tm in
       dest_numeral positive_tm =/ candle_lc_flyspeck_zero &&
       dest_numeral negative_tm =/ candle_lc_flyspeck_zero)
    (dest_list coefficients_tm);;

let candle_lc_bulk_refute_flyspeck_source_profiled
      profile normalize_lhs weighted_inequalities =
  let variables,result,aggregate =
    candle_lc_bulk_compute_flyspeck_source_profiled
      profile normalize_lhs weighted_inequalities in
  profile "final-contradiction-handoff" "begin";
  let coefficients_tm,integer_tm = dest_pair result in
  let positive_tm,negative_tm = dest_pair integer_tm in
  let positive = dest_numeral positive_tm and
      negative = dest_numeral negative_tm in
  if not (candle_lc_all_zero_coefficients coefficients_tm) ||
     not (positive =/ candle_lc_flyspeck_zero) ||
     negative =/ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: aggregate is not a strict contradiction";
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl aggregate) in
  let expected_lhs =
    candle_lc_render_flyspeck_lin_f variables coefficients_tm and
      expected_rhs = candle_lc_render_flyspeck_z integer_tm in
  if not (aconv lhs expected_lhs) || not (aconv rhs expected_rhs) then
    failwith "Flyspeck adapter: public contradiction shape mismatch";
  let n_tm = rand (Arith_int.my_mk_realintconst negative) in
  let final_iff = SPEC n_tm candle_lc_flyspeck_final_inequality in
  let zero_th = Arith_nat.NUM_EQ0_HASH_CONV n_tm in
  let contradiction = EQ_MP final_iff aggregate in
  let final_th = EQ_MP zero_th contradiction in
  profile "final-contradiction-handoff" "end";
  variables,result,final_th;;

let candle_lc_bulk_refute_flyspeck_source
      normalize_lhs weighted_inequalities =
  candle_lc_bulk_refute_flyspeck_source_profiled
    (fun _ _ -> ()) normalize_lhs weighted_inequalities;;

let candle_lc_flyspeck_weight_term weight =
  if weight </ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: negative certificate multiplier"
  else mk_numeral weight;;

(* The legacy Flyspeck checker accumulates target and variable-bound rows by
   variable. Whenever an extended group has zero total lhs coefficient, it
   removes the complete group, including its hypotheses and rhs, from the
   cancellation fold. A later row for that variable starts a fresh group.
   Reproduce that source-row selection before the reflected bulk fold. *)
let candle_lc_select_flyspeck_auxiliary_rows
      normalize_lhs weighted_inequalities =
  let classify ((inequality,weight) as weighted_inequality) =
    let _ = candle_lc_flyspeck_weight_term weight in
    let normalized =
      candle_lc_normalize_flyspeck_inequality normalize_lhs inequality in
    let lhs,_ = dest_binop `(<=):real->real->bool` (concl normalized) in
    let standard_lhs =
      rand (concl (candle_lc_flyspeck_standardize_numerals lhs)) in
    let head,entries_tm = dest_comb standard_lhs in
    if head <> candle_lc_flyspeck_lin_f_const then
      failwith "Flyspeck adapter: auxiliary lhs is not lin_f";
    match dest_list entries_tm with
    | [entry] ->
        let coefficient_tm,variable = dest_pair entry in
        variable,dest_realintconst coefficient_tm */ weight,
        weighted_inequality
    | _ ->
        failwith "Flyspeck adapter: auxiliary lhs is not a singleton" in
  let rec update variable coefficient row groups =
    match groups with
    | [] -> [variable,coefficient,[row]]
    | (group_variable,total,rows)::tail ->
        if aconv variable group_variable then
          let new_total = coefficient +/ total in
          if new_total =/ candle_lc_flyspeck_zero then tail
          else (group_variable,new_total,row::rows)::tail
        else
          (group_variable,total,rows)::
          update variable coefficient row tail in
  let groups =
    List.fold_left
      (fun groups weighted_inequality ->
         let variable,coefficient,row = classify weighted_inequality in
         update variable coefficient row groups)
      [] weighted_inequalities in
  let term_less = Term.(<) in
  let ordered_groups =
    List.sort
      (fun (left,_,_) (right,_,_) ->
         if left = right then 0
         else if term_less left right then -1 else 1)
      groups in
  List.flatten
    (map (fun (_,_,rows) -> List.rev rows) ordered_groups);;

let candle_lc_bulk_refute_flyspeck_terminal_profiled
      profile normalize_lhs precision_constant constraint_inequalities
      auxiliary_inequalities =
  if precision_constant <=/ candle_lc_flyspeck_zero then
    failwith "Flyspeck adapter: nonpositive precision multiplier";
  profile "terminal-number-conversion" "begin";
  let scaled_constraints =
    map
      (fun (inequality,weight) ->
         inequality,
         candle_lc_flyspeck_weight_term (precision_constant */ weight))
      constraint_inequalities and
      auxiliaries =
    map
      (fun (inequality,weight) ->
         inequality,candle_lc_flyspeck_weight_term weight)
      auxiliary_inequalities in
  profile "terminal-number-conversion" "end";
  candle_lc_bulk_refute_flyspeck_source_profiled
    profile normalize_lhs (scaled_constraints @ auxiliaries);;

let candle_lc_bulk_refute_flyspeck_terminal
      normalize_lhs precision_constant constraint_inequalities
      auxiliary_inequalities =
  candle_lc_bulk_refute_flyspeck_terminal_profiled
    (fun _ _ -> ()) normalize_lhs precision_constant
    constraint_inequalities auxiliary_inequalities;;

end;;
