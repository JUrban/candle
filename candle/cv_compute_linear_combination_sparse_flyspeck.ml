(* ========================================================================== *)
(* Flyspeck source adapter for the sparse one-shot LP verdict.                *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE. Source inequalities are connected once to a    *)
(* sparse exact encoding. Kernel.compute checks the complete certificate and  *)
(* the generic soundness theorem performs one final contradiction handoff.    *)
(* ========================================================================== *)

needs "candle/cv_compute_linear_combination_flyspeck.ml";;
needs "candle/cv_compute_linear_combination_sparse_sound.ml";;

module Candle_cv_linear_combination_sparse_flyspeck = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_reify;;
open Candle_cv_linear_combination_bulk;;
open Candle_cv_linear_combination_adapter;;
open Candle_cv_linear_combination_flyspeck;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_linear_combination_sparse_verdict;;
open Candle_cv_linear_combination_sparse_sound;;

let candle_lc_sparse_flyspeck_entry_type = `:num#(num#num)`;;
let candle_lc_sparse_flyspeck_row_type =
  `:num#((num#(num#num))list#(num#num))`;;
let candle_lc_sparse_flyspeck_zero_acc =
  `(([]:(num#(num#num))list),(0,0))`;;
let candle_lc_sparse_flyspeck_all_const =
  rator
    (rator
      `ALL
         (\candle_sparse_encoded_row:
            num#((num#(num#num))list#(num#num)). T)
         ([]:(num#((num#(num#num))list#(num#num)))list)`);;

let rec candle_lc_sparse_flyspeck_index variable index = function
  | [] -> failwith "sparse Flyspeck adapter: variable outside basis"
  | candidate::rest ->
      if aconv variable candidate then index
      else candle_lc_sparse_flyspeck_index variable (index + 1) rest;;

let candle_lc_sparse_el_cache_hits = ref 0;;
let candle_lc_sparse_el_cache_misses = ref 0;;

let candle_lc_sparse_flyspeck_selector_conv variables variables_tm =
  let cache = Hashtbl.create (List.length variables) in
  candle_lc_sparse_el_cache_hits := 0;
  candle_lc_sparse_el_cache_misses := 0;
  fun tm ->
    let head,args = strip_comb tm in
    if not (is_const head) || fst (dest_const head) <> "EL" then
      failwith "sparse Flyspeck adapter: selector conversion";
    let index_tm,list_tm =
      match args with
      | [index_tm;list_tm] -> index_tm,list_tm
      | _ -> failwith "sparse Flyspeck adapter: malformed EL term" in
    if not (aconv list_tm variables_tm) then
      failwith "sparse Flyspeck adapter: unexpected selector basis";
    let index = dest_numeral index_tm in
    try
      let th = Hashtbl.find cache index in
        candle_lc_sparse_el_cache_hits :=
          !candle_lc_sparse_el_cache_hits + 1;
        th
    with Not_found ->
        let th = EL_CONV tm in
        if hyp th <> [] ||
           not (aconv (lhand (concl th)) tm) ||
           not (exists (fun variable -> aconv (rand (concl th)) variable)
                  variables) then
          failwith "sparse Flyspeck adapter: invalid selector theorem";
        Hashtbl.add cache index th;
        candle_lc_sparse_el_cache_misses :=
          !candle_lc_sparse_el_cache_misses + 1;
        th;;

let candle_lc_sparse_el_cache_stats () =
  !candle_lc_sparse_el_cache_hits,!candle_lc_sparse_el_cache_misses;;

let candle_lc_sparse_flyspeck_normalize_conv selector_conv tm =
  let expansion =
    REWRITE_CONV
      [candle_lc_sparse_vec_real_def;
       EL; HD; TL;
       Linear_function.lin_f; ITLIST;
       candle_lc_zreal_def;
       REAL_SUB_RZERO; REAL_SUB_LZERO; REAL_NEG_0;
       REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID] tm in
  let selected = DEPTH_CONV selector_conv (rand (concl expansion)) in
  TRANS expansion selected;;

let candle_lc_reify_sparse_flyspeck_lin_f selector_conv variables lhs =
  candle_lc_check_variables Term.(<) variables;
  let standardize_th = candle_lc_flyspeck_standardize_numerals lhs in
  let standard_lhs = rand (concl standardize_th) in
  let entries =
    candle_lc_dest_entries
      candle_lc_flyspeck_lin_f_const dest_realintconst standard_lhs in
  candle_lc_check_entries Term.(<) variables entries;
  let sparse_entries =
    map
      (fun (_,variable,coefficient) ->
         mk_pair
           (mk_small_numeral
              (candle_lc_sparse_flyspeck_index variable 0 variables),
            candle_lc_z_term coefficient))
      entries in
  let variables_tm = mk_list (variables,`:real`) and
      sparse_entries_tm =
        mk_list (sparse_entries,candle_lc_sparse_flyspeck_entry_type) in
  let exact_tm =
    mk_comb
      (mk_comb (`candle_lc_sparse_vec_real`,variables_tm),
       sparse_entries_tm) in
  let exact_th =
    candle_lc_sparse_flyspeck_normalize_conv selector_conv exact_tm and
      source_th =
    candle_lc_sparse_flyspeck_normalize_conv selector_conv standard_lhs in
  if not (aconv (rand (concl exact_th)) (rand (concl source_th))) then
    failwith "sparse Flyspeck adapter: lhs denotation mismatch";
  sparse_entries_tm,
  TRANS exact_th (TRANS (SYM source_th) (SYM standardize_th));;

let candle_lc_reify_sparse_flyspeck_row selector_conv variables variables_tm
      (inequality,weight) =
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl inequality) in
  let entries,lhs_th =
    candle_lc_reify_sparse_flyspeck_lin_f selector_conv variables lhs and
      integer,rhs_th = candle_lc_reify_flyspeck_integer rhs in
  let exact_lhs =
    mk_comb
      (mk_comb (`candle_lc_sparse_vec_real`,variables_tm),entries) and
      exact_rhs = mk_comb (`candle_lc_zreal`,integer) in
  candle_lc_check_reification "sparse lhs" exact_lhs lhs lhs_th;
  candle_lc_check_reification "sparse rhs" exact_rhs rhs rhs_th;
  let exact_row = mk_pair (weight,mk_pair (entries,integer)) and
      raw_row = candle_lc_row_of_inequality weight inequality in
  let row_real_tm =
    mk_comb
      (mk_comb (`candle_lc_sparse_row_real`,variables_tm),exact_row) in
  let row_expansion =
    REWRITE_CONV[candle_lc_sparse_row_real_def] row_real_tm in
  let row_contents =
    candle_lc_pair_rule (REFL weight)
      (candle_lc_pair_rule lhs_th rhs_th) in
  let row_th = TRANS row_expansion row_contents in
  if not (aconv (rand (concl row_th)) raw_row) then
    failwith "sparse Flyspeck adapter: row denotation mismatch";
  exact_row,raw_row,row_th,inequality;;

let candle_lc_sparse_flyspeck_rows variables weighted_inequalities =
  let variables_tm = mk_list (variables,`:real`) in
  let selector_conv =
    candle_lc_sparse_flyspeck_selector_conv variables variables_tm in
  let rows =
    map
      (candle_lc_reify_sparse_flyspeck_row
        selector_conv variables variables_tm)
      weighted_inequalities in
  let exact_rows =
    mk_list
      (map (fun (row,_,_,_) -> row) rows,
       candle_lc_sparse_flyspeck_row_type) in
  variables_tm,exact_rows,rows;;

let candle_lc_sparse_flyspeck_all_rows variables_tm exact_rows rows =
  let row_real_fun =
    mk_comb (`candle_lc_sparse_row_real`,variables_tm) in
  let row_var =
    mk_var
      ("candle_sparse_encoded_row",candle_lc_sparse_flyspeck_row_type) in
  let predicate =
    mk_abs
      (row_var,
       mk_comb
         (`candle_lc_real_row_holds`,mk_comb (row_real_fun,row_var))) in
  let exact_rows_and_theorems =
    map
      (fun (exact_row,raw_row,row_th,inequality) ->
         let denoted_row =
           mk_comb (row_real_fun,exact_row) in
         let raw_holds = candle_lc_row_holds_rule raw_row inequality in
         let holds_eq =
           AP_TERM `candle_lc_real_row_holds` row_th in
         let denoted_holds = EQ_MP (SYM holds_eq) raw_holds in
         let predicate_beta = BETA_CONV (mk_comb (predicate,exact_row)) in
         exact_row,EQ_MP (SYM predicate_beta) denoted_holds)
      rows in
  let all_predicate rows_tm =
    mk_comb
      (mk_comb (candle_lc_sparse_flyspeck_all_const,predicate),rows_tm) in
  let empty_rows =
    mk_list ([],candle_lc_sparse_flyspeck_row_type) in
  let empty_eq = ONCE_REWRITE_CONV[ALL] (all_predicate empty_rows) in
  let empty_th = EQ_MP (SYM empty_eq) TRUTH in
  let built_rows,all_exact =
    List.fold_right
      (fun (row,row_th) (tail,tail_th) ->
         let rows_tm = mk_cons row tail in
         let all_eq =
           ONCE_REWRITE_CONV[ALL] (all_predicate rows_tm) in
         rows_tm,EQ_MP (SYM all_eq) (CONJ row_th tail_th))
      exact_rows_and_theorems (empty_rows,empty_th) in
  if not (aconv built_rows exact_rows) then
    failwith "sparse Flyspeck adapter: exact row list mismatch";
  let all_map =
    REWRITE_RULE[o_DEF]
      (ISPECL [`candle_lc_real_row_holds`;row_real_fun;exact_rows]
        ALL_MAP) in
  if not (aconv (rand (concl all_map)) (concl all_exact)) then
    failwith "sparse Flyspeck adapter: ALL_MAP premise mismatch";
  EQ_MP (SYM all_map) all_exact;;

let candle_lc_sparse_flyspeck_compute_verdict exact_rows =
  let acc_rep =
    REWRITE_CONV
      [candle_cv_lc_sparse_acc_def;
       candle_cv_lc_sparse_vec_def;
       candle_cv_lc_sparse_entry_def;
       candle_cv_lc_z_def]
      (mk_comb
        (`candle_cv_lc_sparse_acc`,candle_lc_sparse_flyspeck_zero_acc)) in
  let rows_rep =
    REWRITE_CONV
      [candle_cv_lc_sparse_rows_def;
       candle_cv_lc_sparse_row_def;
       candle_cv_lc_sparse_acc_def;
       candle_cv_lc_sparse_vec_def;
       candle_cv_lc_sparse_entry_def;
       candle_cv_lc_z_def]
      (mk_comb (`candle_cv_lc_sparse_rows`,exact_rows)) in
  let concrete_tm =
    mk_comb
      (mk_comb
        (`candle_cv_lc_sparse_fold_verdict`,rand (concl acc_rep)),
       rand (concl rows_rep)) in
  let computed = compute candle_cv_lc_sparse_compute_eqs concrete_tm in
  let logical_lhs =
    MK_COMB
      (AP_TERM `candle_cv_lc_sparse_fold_verdict` acc_rep,rows_rep) in
  let logical = TRANS logical_lhs computed in
  let result = rand (concl logical) in
  if not (aconv result `Cexp_num 1`) then
    failwith "sparse Flyspeck adapter: computed certificate is not infeasible";
  TRANS logical (AP_TERM `Cexp_num` (ARITH_RULE `1 = SUC 0`));;

let candle_lc_sparse_refute_flyspeck_source_profiled
      profile normalize_lhs weighted_inequalities =
  profile "sparse-source-normalization-variable-discovery" "begin";
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
  profile "sparse-source-normalization-variable-discovery" "end";
  profile "sparse-source-number-conversion" "begin";
  let variables_tm,exact_rows,rows =
    candle_lc_sparse_flyspeck_rows variables normalized in
  profile "sparse-source-number-conversion" "end";
  profile "sparse-source-proof-preparation" "begin";
  let all_rows =
    candle_lc_sparse_flyspeck_all_rows variables_tm exact_rows rows in
  profile "sparse-source-proof-preparation" "end";
  profile "sparse-kernel-compute" "begin";
  let computed = candle_lc_sparse_flyspeck_compute_verdict exact_rows in
  profile "sparse-kernel-compute" "end";
  profile "sparse-theorem-handoff" "begin";
  let not_all =
    MATCH_MP
      (SPECL [variables_tm;exact_rows]
        candle_cv_lc_sparse_fold_verdict_sound)
      computed in
  let contradiction = MP (NOT_ELIM not_all) all_rows in
  profile "sparse-theorem-handoff" "end";
  variables,exact_rows,contradiction;;

let candle_lc_sparse_refute_flyspeck_source normalize_lhs rows =
  candle_lc_sparse_refute_flyspeck_source_profiled
    (fun _ _ -> ()) normalize_lhs rows;;

let candle_lc_sparse_refute_flyspeck_terminal_profiled
      profile normalize_lhs precision_constant constraint_inequalities
      auxiliary_inequalities =
  if precision_constant <=/ candle_lc_flyspeck_zero then
    failwith "sparse Flyspeck adapter: nonpositive precision multiplier";
  profile "sparse-terminal-number-conversion" "begin";
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
  profile "sparse-terminal-number-conversion" "end";
  candle_lc_sparse_refute_flyspeck_source_profiled
    profile normalize_lhs (scaled_constraints @ auxiliaries);;

let candle_lc_sparse_refute_flyspeck_terminal
      normalize_lhs precision_constant constraints auxiliaries =
  candle_lc_sparse_refute_flyspeck_terminal_profiled
    (fun _ _ -> ()) normalize_lhs precision_constant constraints auxiliaries;;

end;;
