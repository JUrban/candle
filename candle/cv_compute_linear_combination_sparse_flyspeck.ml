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

let candle_lc_sparse_flyspeck_indexer variables =
  candle_lc_check_variables Term.(<) variables;
  let indices = Hashtbl.create (List.length variables) in
  let rec add index = function
    | [] -> ()
    | variable::rest ->
        Hashtbl.add indices variable (index,variable);
        add (index + 1) rest in
  add 0 variables;
  fun variable ->
    try
      let index,canonical = Hashtbl.find indices variable in
      if not (aconv canonical variable) then
        failwith "sparse Flyspeck adapter: invalid variable index";
      index
    with Not_found ->
      failwith "sparse Flyspeck adapter: variable outside basis";;

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

let candle_lc_sparse_flyspeck_prepare_selectors
      variables variables_tm selector_conv =
  let rec prepare index = function
    | [] -> ()
    | _::rest ->
        let index_tm = mk_small_numeral index in
        let selector_tm =
          mk_comb
            (mk_comb (`EL:num->real list->real`,index_tm),variables_tm) in
        let _ = selector_conv selector_tm in
        prepare (index + 1) rest in
  prepare 0 variables;;

let candle_lc_sparse_integer_cache_hits = ref 0;;
let candle_lc_sparse_integer_cache_misses = ref 0;;

(* A certificate repeats a small vocabulary of exact integer coefficients
   across many source rows.  Keep this cache local to one conversion, and
   recheck the exact requested equality on every hit. *)
let candle_lc_sparse_flyspeck_integer_conv () =
  let cache = Hashtbl.create 67 in
  candle_lc_sparse_integer_cache_hits := 0;
  candle_lc_sparse_integer_cache_misses := 0;
  fun integer_tm ->
    try
      let integer,integer_th = Hashtbl.find cache integer_tm in
      let expected = mk_comb (`candle_lc_zreal`,integer) in
      candle_lc_check_reification
        "cached sparse integer" expected integer_tm integer_th;
      candle_lc_sparse_integer_cache_hits :=
        !candle_lc_sparse_integer_cache_hits + 1;
      integer,integer_th
    with Not_found ->
      let result = candle_lc_reify_flyspeck_integer integer_tm in
      Hashtbl.add cache integer_tm result;
      candle_lc_sparse_integer_cache_misses :=
        !candle_lc_sparse_integer_cache_misses + 1;
      result;;

let candle_lc_sparse_integer_cache_stats () =
  !candle_lc_sparse_integer_cache_hits,
  !candle_lc_sparse_integer_cache_misses;;

let candle_lc_sparse_lhs_cache_hits = ref 0;;
let candle_lc_sparse_lhs_cache_misses = ref 0;;

(* Development profiling for the real master-construction boundary.  These
   timers never select or authorize a theorem; they only account successful
   host-side proof construction. *)
let candle_lc_sparse_profile_lin_standardize = ref 0.0;;
let candle_lc_sparse_profile_entries_total = ref 0.0;;
let candle_lc_sparse_profile_entry_integer = ref 0.0;;
let candle_lc_sparse_profile_entry_selector = ref 0.0;;
let candle_lc_sparse_profile_entry_expansion = ref 0.0;;
let candle_lc_sparse_profile_entry_congruence = ref 0.0;;
let candle_lc_sparse_profile_lin_structural = ref 0.0;;
let candle_lc_sparse_profile_master_lhs = ref 0.0;;
let candle_lc_sparse_profile_master_rhs = ref 0.0;;
let candle_lc_sparse_profile_master_checks = ref 0.0;;
let candle_lc_sparse_profile_master_row = ref 0.0;;

let candle_lc_sparse_profile_time accumulator action =
  let started = Unix.gettimeofday() in
  try
    let result = action () in
    accumulator := !accumulator +. (Unix.gettimeofday() -. started);
    result
  with failure ->
    (accumulator := !accumulator +. (Unix.gettimeofday() -. started);
     raise failure);;

let candle_lc_sparse_master_profile_reset () =
  List.iter
    (fun counter -> counter := 0.0)
    [candle_lc_sparse_profile_lin_standardize;
     candle_lc_sparse_profile_entries_total;
     candle_lc_sparse_profile_entry_integer;
     candle_lc_sparse_profile_entry_selector;
     candle_lc_sparse_profile_entry_expansion;
     candle_lc_sparse_profile_entry_congruence;
     candle_lc_sparse_profile_lin_structural;
     candle_lc_sparse_profile_master_lhs;
     candle_lc_sparse_profile_master_rhs;
     candle_lc_sparse_profile_master_checks;
     candle_lc_sparse_profile_master_row];;

let candle_lc_sparse_master_profile_stats () =
  [("lin-standardize",!candle_lc_sparse_profile_lin_standardize);
   ("entries-total",!candle_lc_sparse_profile_entries_total);
   ("entry-integer",!candle_lc_sparse_profile_entry_integer);
   ("entry-selector",!candle_lc_sparse_profile_entry_selector);
   ("entry-expansion",!candle_lc_sparse_profile_entry_expansion);
   ("entry-congruence",!candle_lc_sparse_profile_entry_congruence);
   ("lin-structural",!candle_lc_sparse_profile_lin_structural);
   ("master-lhs",!candle_lc_sparse_profile_master_lhs);
   ("master-rhs",!candle_lc_sparse_profile_master_rhs);
   ("master-checks",!candle_lc_sparse_profile_master_checks);
   ("master-row",!candle_lc_sparse_profile_master_row)];;

type candle_lc_sparse_flyspeck_context = {
  candle_sparse_variables: term list;
  candle_sparse_variables_tm: term;
  candle_sparse_variable_index: term -> int;
  candle_sparse_selector_conv: term -> thm;
  candle_sparse_integer_conv: term -> term * thm;
  candle_sparse_lhs_cache: (term,term * thm) Hashtbl.t
};;

let candle_lc_sparse_flyspeck_context_profiled profile variables =
  let variables_tm = mk_list (variables,`:real`) in
  let variable_index = candle_lc_sparse_flyspeck_indexer variables in
  let selector_conv =
    candle_lc_sparse_flyspeck_selector_conv variables variables_tm in
  profile "sparse-selector-proof-preparation" "begin";
  candle_lc_sparse_flyspeck_prepare_selectors
    variables variables_tm selector_conv;
  profile "sparse-selector-proof-preparation" "end";
  let integer_conv = candle_lc_sparse_flyspeck_integer_conv () in
  candle_lc_sparse_lhs_cache_hits := 0;
  candle_lc_sparse_lhs_cache_misses := 0;
  {candle_sparse_variables = variables;
   candle_sparse_variables_tm = variables_tm;
   candle_sparse_variable_index = variable_index;
   candle_sparse_selector_conv = selector_conv;
   candle_sparse_integer_conv = integer_conv;
   candle_sparse_lhs_cache = Hashtbl.create 1021};;

let candle_lc_sparse_flyspeck_context variables =
  candle_lc_sparse_flyspeck_context_profiled (fun _ _ -> ()) variables;;

let candle_lc_sparse_lhs_cache_stats () =
  !candle_lc_sparse_lhs_cache_hits,!candle_lc_sparse_lhs_cache_misses;;

let candle_lc_sparse_flyspeck_nil = prove
 (`!candle_sparse_basis:real list.
     candle_lc_sparse_vec_real candle_sparse_basis [] = lin_f []`,
  REWRITE_TAC[candle_lc_sparse_vec_real_def;
              Linear_function.LIN_F_EMPTY]);;

let candle_lc_sparse_flyspeck_cons = prove
 (`!(candle_sparse_basis:real list) (candle_sparse_i:num)
     (candle_sparse_z:num#num)
     (candle_sparse_tail:(num#(num#num))list)
     (candle_source_c:real) (candle_source_x:real)
     (candle_source_tail:(real#real)list).
     candle_lc_zreal candle_sparse_z = candle_source_c
     ==> EL candle_sparse_i candle_sparse_basis = candle_source_x
     ==> candle_lc_sparse_vec_real candle_sparse_basis candle_sparse_tail =
         lin_f candle_source_tail
     ==> candle_lc_sparse_vec_real candle_sparse_basis
           (CONS (candle_sparse_i,candle_sparse_z) candle_sparse_tail) =
         lin_f (CONS (candle_source_c,candle_source_x)
                     candle_source_tail)`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[candle_lc_sparse_vec_real_cons;
                  Linear_function.LIN_F_CONS; FST; SND]);;

(* Reify the source entry list before applying [lin_f].  This keeps the
   concrete proof at the list/pair level: one generic theorem below connects
   the whole list to its real denotation, so the host does not reconstruct a
   growing arithmetic sum for every source row. *)
(* Keep the clauses as separately typechecked quotations.  Candle's frontend
   currently cannot infer the shared polymorphic recursive constant through
   the single conjunction quotation accepted by native HOL Light. *)
let candle_lc_sparse_source_entries_nil_clause =
 `!candle_sparse_basis:real list.
    candle_lc_sparse_source_entries candle_sparse_basis
      ([]:(num#(num#num))list) = ([]:(real#real)list)`;;

let candle_lc_sparse_source_entries_cons_clause =
 `!(candle_sparse_basis:real list)
    (candle_sparse_entry:num#(num#num))
    (candle_sparse_tail:(num#(num#num))list).
    candle_lc_sparse_source_entries candle_sparse_basis
      (CONS candle_sparse_entry candle_sparse_tail) =
    CONS
      (candle_lc_zreal (SND candle_sparse_entry),
       EL (FST candle_sparse_entry) candle_sparse_basis)
      (candle_lc_sparse_source_entries candle_sparse_basis
         candle_sparse_tail)`;;

let candle_lc_sparse_source_entries_def =
  new_recursive_definition list_RECURSION
    (mk_conj
      (candle_lc_sparse_source_entries_nil_clause,
       candle_lc_sparse_source_entries_cons_clause));;

let candle_lc_sparse_source_entries_denotation = prove
 (`!candle_sparse_entries candle_sparse_basis.
     candle_lc_sparse_vec_real candle_sparse_basis candle_sparse_entries =
     lin_f
       (candle_lc_sparse_source_entries candle_sparse_basis
          candle_sparse_entries)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_lc_sparse_vec_real_def;
                candle_lc_sparse_source_entries_def;
                Linear_function.LIN_F_EMPTY];
    GEN_TAC THEN
    ASM_REWRITE_TAC[candle_lc_sparse_vec_real_cons;
                    candle_lc_sparse_source_entries_def;
                    Linear_function.LIN_F_CONS; FST; SND]]);;

(* Construct the encoded and authenticated source lists in lockstep.  Each
   step uses one exact coefficient equality and one cached, checked EL
   theorem.  Only list and pair congruences are built here; the once-proved
   denotation theorem above supplies the complete arithmetic equality. *)
let candle_lc_reify_sparse_flyspeck_entries
      integer_conv selector_conv variable_index variables_tm entries =
  let rec build = function
    | [] ->
        let sparse_tail = mk_list ([],candle_lc_sparse_flyspeck_entry_type) and
            source_tail = mk_list ([],`:real#real`) in
        sparse_tail,source_tail,
        REWRITE_CONV[candle_lc_sparse_source_entries_def]
          (mk_comb
            (mk_comb
              (`candle_lc_sparse_source_entries`,variables_tm),
             sparse_tail))
    | (coefficient,variable,_)::rest ->
        let sparse_tail,source_tail,tail_th = build rest in
        let sparse_index =
          mk_small_numeral (variable_index variable) in
        let sparse_z,coefficient_th =
          candle_lc_sparse_profile_time
            candle_lc_sparse_profile_entry_integer
            (fun () -> integer_conv coefficient) in
        let selector_tm =
          mk_comb
            (mk_comb (`EL:num->real list->real`,sparse_index),variables_tm) in
        let selector_th =
          candle_lc_sparse_profile_time
            candle_lc_sparse_profile_entry_selector
            (fun () -> selector_conv selector_tm) in
        let sparse_entry = mk_pair (sparse_index,sparse_z) and
            source_entry = mk_pair (coefficient,variable) in
        let sparse_entries = mk_cons sparse_entry sparse_tail and
            source_entries = mk_cons source_entry source_tail in
        let source_map_tm =
          mk_comb
            (mk_comb
              (`candle_lc_sparse_source_entries`,variables_tm),
             sparse_entries) in
        let source_expansion =
          candle_lc_sparse_profile_time
            candle_lc_sparse_profile_entry_expansion
            (fun () ->
              REWRITE_RULE[FST;SND]
                (ONCE_REWRITE_CONV[candle_lc_sparse_source_entries_def]
                  source_map_tm)) in
        let source_cons_th =
          candle_lc_sparse_profile_time
            candle_lc_sparse_profile_entry_congruence
            (fun () ->
              let source_head_th =
                candle_lc_pair_rule coefficient_th selector_th in
              MK_BINOP
                `(CONS):(real#real)->(real#real)list->(real#real)list`
                (source_head_th,tail_th)) in
        sparse_entries,source_entries,
        TRANS source_expansion source_cons_th in
  build entries;;

let candle_lc_reify_sparse_flyspeck_lin_f
      integer_conv selector_conv variable_index variables_tm lhs =
  let standardize_th =
    candle_lc_sparse_profile_time
      candle_lc_sparse_profile_lin_standardize
      (fun () -> candle_lc_flyspeck_standardize_numerals lhs) in
  let standard_lhs = rand (concl standardize_th) in
  let entries =
    candle_lc_dest_entries
      candle_lc_flyspeck_lin_f_const dest_realintconst standard_lhs in
  let entry_variables = map (fun (_,variable,_) -> variable) entries in
  if not (candle_lc_strictly_sorted Term.(<) entry_variables) then
    failwith "sparse Flyspeck adapter: lin_f variables are not sorted";
  let sparse_entries_tm,source_entries_tm,source_entries_th =
    candle_lc_sparse_profile_time
      candle_lc_sparse_profile_entries_total
      (fun () ->
        candle_lc_reify_sparse_flyspeck_entries
          integer_conv selector_conv variable_index variables_tm entries) in
  let source_head,source_terms_tm = dest_comb standard_lhs in
  if source_head <> candle_lc_flyspeck_lin_f_const ||
     not (aconv source_entries_tm source_terms_tm) then
    failwith "sparse Flyspeck adapter: structural source list mismatch";
  let exact_tm =
    mk_comb
      (mk_comb (`candle_lc_sparse_vec_real`,variables_tm),
       sparse_entries_tm) in
  candle_lc_sparse_profile_time
    candle_lc_sparse_profile_lin_structural
    (fun () ->
      let structural_th =
        TRANS
          (SPECL [sparse_entries_tm;variables_tm]
            candle_lc_sparse_source_entries_denotation)
          (AP_TERM candle_lc_flyspeck_lin_f_const source_entries_th) in
      if hyp structural_th <> [] ||
         not (aconv (concl structural_th) (mk_eq (exact_tm,standard_lhs))) then
        failwith "sparse Flyspeck adapter: structural denotation mismatch";
      sparse_entries_tm,TRANS structural_th (SYM standardize_th));;

let candle_lc_reify_sparse_flyspeck_lin_f_cached context lhs =
  try
    let entries,lhs_th = Hashtbl.find context.candle_sparse_lhs_cache lhs in
    let exact_lhs =
      mk_comb
        (mk_comb
          (`candle_lc_sparse_vec_real`,context.candle_sparse_variables_tm),
         entries) in
    candle_lc_check_reification "cached sparse lhs" exact_lhs lhs lhs_th;
    candle_lc_sparse_lhs_cache_hits := !candle_lc_sparse_lhs_cache_hits + 1;
    entries,lhs_th
  with Not_found ->
    let result =
      candle_lc_reify_sparse_flyspeck_lin_f
        context.candle_sparse_integer_conv
        context.candle_sparse_selector_conv
        context.candle_sparse_variable_index
        context.candle_sparse_variables_tm lhs in
    Hashtbl.add context.candle_sparse_lhs_cache lhs result;
    candle_lc_sparse_lhs_cache_misses :=
      !candle_lc_sparse_lhs_cache_misses + 1;
    result;;

let candle_lc_sparse_flyspeck_row_denotation
      variables_tm entries lhs_th integer rhs_th weight =
  let exact_row = mk_pair (weight,mk_pair (entries,integer)) in
  let row_real_tm =
    mk_comb
      (mk_comb (`candle_lc_sparse_row_real`,variables_tm),exact_row) in
  let row_expansion =
    REWRITE_CONV[candle_lc_sparse_row_real_def] row_real_tm in
  let row_contents =
    candle_lc_pair_rule (REFL weight)
      (candle_lc_pair_rule lhs_th rhs_th) in
  TRANS row_expansion row_contents;;

let candle_lc_finish_sparse_flyspeck_row
      variables_tm entries lhs_th integer rhs_th (inequality,weight) =
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl inequality) in
  let exact_lhs =
    mk_comb
      (mk_comb (`candle_lc_sparse_vec_real`,variables_tm),entries) and
      exact_rhs = mk_comb (`candle_lc_zreal`,integer) in
  candle_lc_check_reification "sparse lhs" exact_lhs lhs lhs_th;
  candle_lc_check_reification "sparse rhs" exact_rhs rhs rhs_th;
  let exact_row = mk_pair (weight,mk_pair (entries,integer)) and
      raw_row = candle_lc_row_of_inequality weight inequality in
  let row_th =
    candle_lc_sparse_flyspeck_row_denotation
      variables_tm entries lhs_th integer rhs_th weight in
  if not (aconv (rand (concl row_th)) raw_row) then
    failwith "sparse Flyspeck adapter: row denotation mismatch";
  exact_row,raw_row,row_th,inequality;;

let candle_lc_reify_sparse_flyspeck_row context (inequality,weight) =
  let lhs,rhs = dest_binop `(<=):real->real->bool` (concl inequality) in
  let entries,lhs_th =
    candle_lc_reify_sparse_flyspeck_lin_f_cached context lhs and
      integer,rhs_th = context.candle_sparse_integer_conv rhs in
  candle_lc_finish_sparse_flyspeck_row
    context.candle_sparse_variables_tm entries lhs_th integer rhs_th
    (inequality,weight);;

type candle_lc_sparse_flyspeck_master_entry = {
  candle_sparse_source_conclusion: term;
  candle_sparse_source_entries: term;
  candle_sparse_source_lhs_th: thm;
  candle_sparse_source_integer: term;
  candle_sparse_source_rhs_th: thm;
  candle_sparse_source_row_th: thm
};;

type candle_lc_sparse_flyspeck_master = {
  candle_sparse_master_context: candle_lc_sparse_flyspeck_context;
  candle_sparse_master_entries: candle_lc_sparse_flyspeck_master_entry array;
  candle_sparse_master_indices: (term,int * term) Hashtbl.t
};;

let candle_lc_sparse_flyspeck_master_profiled
      profile context weighted_inequalities =
  profile "sparse-master-row-preparation" "begin";
  profile "sparse-master-source-deduplication" "begin";
  let source_conclusions =
    setify Term.(<)
      (map (fun (inequality,_) -> concl inequality) weighted_inequalities) in
  profile "sparse-master-source-deduplication" "end";
  let make_entry source_conclusion =
    let inequality,_ =
      find
        (fun (candidate,_) ->
           aconv (concl candidate) source_conclusion)
        weighted_inequalities in
    let lhs,rhs =
      dest_binop `(<=):real->real->bool` (concl inequality) in
    let entries,lhs_th =
      candle_lc_sparse_profile_time
        candle_lc_sparse_profile_master_lhs
        (fun () ->
          candle_lc_reify_sparse_flyspeck_lin_f_cached context lhs) in
    let integer,rhs_th =
      candle_lc_sparse_profile_time
        candle_lc_sparse_profile_master_rhs
        (fun () -> context.candle_sparse_integer_conv rhs) in
    let exact_lhs =
      mk_comb
        (mk_comb
          (`candle_lc_sparse_vec_real`,context.candle_sparse_variables_tm),
         entries) and
        exact_rhs = mk_comb (`candle_lc_zreal`,integer) in
    candle_lc_sparse_profile_time
      candle_lc_sparse_profile_master_checks
      (fun () ->
        candle_lc_check_reification "master sparse lhs" exact_lhs lhs lhs_th;
        candle_lc_check_reification "master sparse rhs" exact_rhs rhs rhs_th);
    let weight_var =
      variant (frees source_conclusion)
        (mk_var ("candle_sparse_weight",`:num`)) in
    let row_th =
      candle_lc_sparse_profile_time
        candle_lc_sparse_profile_master_row
        (fun () ->
          GEN weight_var
            (candle_lc_sparse_flyspeck_row_denotation
              context.candle_sparse_variables_tm entries lhs_th integer rhs_th
              weight_var)) in
    if hyp row_th <> [] then
      failwith "sparse Flyspeck master: row theorem has assumptions";
    {candle_sparse_source_conclusion = source_conclusion;
     candle_sparse_source_entries = entries;
     candle_sparse_source_lhs_th = lhs_th;
     candle_sparse_source_integer = integer;
     candle_sparse_source_rhs_th = rhs_th;
     candle_sparse_source_row_th = row_th} in
  profile "sparse-master-authenticated-row-theorems" "begin";
  let entry_list = map make_entry source_conclusions in
  profile "sparse-master-authenticated-row-theorems" "end";
  let entries = Array.of_list entry_list and
      indices = Hashtbl.create (List.length entry_list) in
  let rec add_indices index = function
    | [] -> ()
    | entry::rest ->
        Hashtbl.add indices entry.candle_sparse_source_conclusion
          (index,entry.candle_sparse_source_conclusion);
        add_indices (index + 1) rest in
  add_indices 0 entry_list;
  profile "sparse-master-row-preparation" "end";
  {candle_sparse_master_context = context;
   candle_sparse_master_entries = entries;
   candle_sparse_master_indices = indices};;

let candle_lc_sparse_flyspeck_master context weighted_inequalities =
  candle_lc_sparse_flyspeck_master_profiled
    (fun _ _ -> ()) context weighted_inequalities;;

let candle_lc_sparse_flyspeck_master_size master =
  Array.length master.candle_sparse_master_entries;;

let candle_lc_sparse_flyspeck_master_index master source_conclusion =
  try
    let index,canonical =
      Hashtbl.find master.candle_sparse_master_indices source_conclusion in
    if not (aconv canonical source_conclusion) then
      failwith "sparse Flyspeck master: invalid source index";
    index
  with Not_found ->
    failwith "sparse Flyspeck master: undeclared source row";;

let candle_lc_sparse_flyspeck_plan master weighted_inequalities =
  map
    (fun (inequality,weight) ->
       candle_lc_sparse_flyspeck_master_index master (concl inequality),
       (inequality,weight))
    weighted_inequalities;;

let candle_lc_resolve_sparse_flyspeck_master_row
      master (index,(inequality,weight)) =
  let entry = Array.get master.candle_sparse_master_entries index in
  if not
       (aconv entry.candle_sparse_source_conclusion (concl inequality)) then
    failwith "sparse Flyspeck master: plan/source mismatch";
  entry,(inequality,weight);;

let candle_lc_reify_resolved_sparse_flyspeck_master_row
      master (entry,(inequality,weight)) =
  let exact_row =
    mk_pair
      (weight,
       mk_pair
         (entry.candle_sparse_source_entries,
          entry.candle_sparse_source_integer)) and
      raw_row = candle_lc_row_of_inequality weight inequality in
  let row_th = SPEC weight entry.candle_sparse_source_row_th in
  if hyp row_th <> [] ||
     not (aconv (rand (concl row_th)) raw_row) then
    failwith "sparse Flyspeck master: row denotation mismatch";
  exact_row,raw_row,row_th,inequality;;

let candle_lc_reify_sparse_flyspeck_master_row master planned_row =
  candle_lc_reify_resolved_sparse_flyspeck_master_row master
    (candle_lc_resolve_sparse_flyspeck_master_row master planned_row);;

let candle_lc_sparse_flyspeck_rows_with_master_profiled
      profile master plan =
  profile "sparse-master-row-instantiation" "begin";
  profile "sparse-master-plan-resolution" "begin";
  let resolved =
    map (candle_lc_resolve_sparse_flyspeck_master_row master) plan in
  profile "sparse-master-plan-resolution" "end";
  profile "sparse-master-row-denotation" "begin";
  let rows =
    map (candle_lc_reify_resolved_sparse_flyspeck_master_row master) resolved in
  profile "sparse-master-row-denotation" "end";
  profile "sparse-master-row-instantiation" "end";
  let exact_rows =
    mk_list
      (map (fun (row,_,_,_) -> row) rows,
       candle_lc_sparse_flyspeck_row_type) in
  master.candle_sparse_master_context.candle_sparse_variables_tm,
  exact_rows,rows;;

let candle_lc_sparse_flyspeck_rows_with_context_profiled
      profile context weighted_inequalities =
  profile "sparse-row-reification" "begin";
  let rows =
    map (candle_lc_reify_sparse_flyspeck_row context) weighted_inequalities in
  profile "sparse-row-reification" "end";
  let exact_rows =
    mk_list
      (map (fun (row,_,_,_) -> row) rows,
       candle_lc_sparse_flyspeck_row_type) in
  context.candle_sparse_variables_tm,exact_rows,rows;;

let candle_lc_sparse_flyspeck_rows_profiled
      profile variables weighted_inequalities =
  let context =
    candle_lc_sparse_flyspeck_context_profiled profile variables in
  candle_lc_sparse_flyspeck_rows_with_context_profiled
    profile context weighted_inequalities;;

let candle_lc_sparse_flyspeck_rows variables weighted_inequalities =
  candle_lc_sparse_flyspeck_rows_profiled
    (fun _ _ -> ()) variables weighted_inequalities;;

let candle_lc_sparse_flyspeck_all_rows_profiled
      profile variables_tm exact_rows rows =
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
  profile "sparse-source-row-holds" "begin";
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
  profile "sparse-source-row-holds" "end";
  let all_predicate rows_tm =
    mk_comb
      (mk_comb (candle_lc_sparse_flyspeck_all_const,predicate),rows_tm) in
  let empty_rows =
    mk_list ([],candle_lc_sparse_flyspeck_row_type) in
  let empty_eq = ONCE_REWRITE_CONV[ALL] (all_predicate empty_rows) in
  let empty_th = EQ_MP (SYM empty_eq) TRUTH in
  profile "sparse-all-list-construction" "begin";
  let built_rows,all_exact =
    List.fold_right
      (fun (row,row_th) (tail,tail_th) ->
         let rows_tm = mk_cons row tail in
         let all_eq =
           ONCE_REWRITE_CONV[ALL] (all_predicate rows_tm) in
         rows_tm,EQ_MP (SYM all_eq) (CONJ row_th tail_th))
      exact_rows_and_theorems (empty_rows,empty_th) in
  profile "sparse-all-list-construction" "end";
  if not (aconv built_rows exact_rows) then
    failwith "sparse Flyspeck adapter: exact row list mismatch";
  profile "sparse-all-map-bridge" "begin";
  let all_map =
    REWRITE_RULE[o_DEF]
      (ISPECL [`candle_lc_real_row_holds`;row_real_fun;exact_rows]
        ALL_MAP) in
  if not (aconv (rand (concl all_map)) (concl all_exact)) then
    failwith "sparse Flyspeck adapter: ALL_MAP premise mismatch";
  let result = EQ_MP (SYM all_map) all_exact in
  profile "sparse-all-map-bridge" "end";
  result;;

let candle_lc_sparse_flyspeck_all_rows variables_tm exact_rows rows =
  candle_lc_sparse_flyspeck_all_rows_profiled
    (fun _ _ -> ()) variables_tm exact_rows rows;;

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

let candle_lc_sparse_refute_flyspeck_prepared_profiled
      profile context variables_tm exact_rows rows =
  profile "sparse-source-proof-preparation" "begin";
  let all_rows =
    candle_lc_sparse_flyspeck_all_rows_profiled
      profile variables_tm exact_rows rows in
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
  context.candle_sparse_variables,exact_rows,contradiction;;

let candle_lc_sparse_refute_flyspeck_normalized_with_context_profiled
      profile context normalized =
  profile "sparse-source-number-conversion" "begin";
  let variables_tm,exact_rows,rows =
    candle_lc_sparse_flyspeck_rows_with_context_profiled
      profile context normalized in
  profile "sparse-source-number-conversion" "end";
  candle_lc_sparse_refute_flyspeck_prepared_profiled
    profile context variables_tm exact_rows rows;;

let candle_lc_sparse_refute_flyspeck_plan_with_master_profiled
      profile master plan =
  profile "sparse-source-number-conversion" "begin";
  let variables_tm,exact_rows,rows =
    candle_lc_sparse_flyspeck_rows_with_master_profiled
      profile master plan in
  profile "sparse-source-number-conversion" "end";
  candle_lc_sparse_refute_flyspeck_prepared_profiled
    profile master.candle_sparse_master_context
    variables_tm exact_rows rows;;

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
  let context =
    candle_lc_sparse_flyspeck_context_profiled profile variables in
  let variables_tm,exact_rows,rows =
    candle_lc_sparse_flyspeck_rows_with_context_profiled
      profile context normalized in
  profile "sparse-source-number-conversion" "end";
  candle_lc_sparse_refute_flyspeck_prepared_profiled
    profile context variables_tm exact_rows rows;;

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
