(* ========================================================================== *)
(* Typed coverage and deterministic replay skeleton for tame-graph reflection. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file proves only a general logical        *)
(* skeleton.  In particular, none of its abstract pruning, invariant, or      *)
(* archive premises is assumed for the Flyspeck production constants here.    *)
(* ========================================================================== *)

needs "Library/rstc.ml";;

(* Goal-driven helpers used by the replay induction.  They live outside the     *)
(* theorem namespace because they are ML tactics, not logical constants.        *)

let candle_tame_list_cases_tac list_name head_name tail_name =
  W (fun (_,goal) ->
    let list_tm =
      try find_term
        (fun tm -> is_var tm && fst(dest_var tm) = list_name) goal
      with Failure _ ->
        try lhs (find_term
          (fun tm -> is_eq tm && is_var(lhs tm) &&
             is_const(rhs tm) && fst(dest_const(rhs tm)) = "NIL") goal)
        with Failure _ ->
          failwith ("candle_tame_list_cases_tac: missing " ^ list_name) in
    let _,[element_ty] = dest_type(type_of list_tm) in
    let head_tm = mk_var(head_name,element_ty) in
    let tail_tm = mk_var(tail_name,type_of list_tm) in
    MP_TAC (ISPEC list_tm list_CASES) THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (X_CHOOSE_THEN head_tm
        (X_CHOOSE_THEN tail_tm SUBST_ALL_TAC))));;

let candle_tame_match_replay_ih_tac assumption_label =
  USE_THEN assumption_label (fun replay_ih ->
    W (fun (assumptions,goal) ->
      let terms = goal :: List.map (fun (_,th) -> concl th) assumptions in
      let replay_eq =
        try tryfind
          (find_term (fun tm -> is_eq tm &&
             can (find_term (fun subtm ->
               let head,_ = strip_comb subtm in
               is_const head &&
               fst(dest_const head) = "candle_tame_replay")) (lhs tm) &&
             is_comb(rhs tm) && is_const(rator(rhs tm)) &&
             fst(dest_const(rator(rhs tm))) = "SOME")) terms
        with Failure _ ->
          failwith "candle_tame_match_replay_ih_tac: missing replay result" in
      let replay_app = find_term
        (fun tm ->
          let head,args = strip_comb tm in
          is_const head && fst(dest_const head) = "candle_tame_replay" &&
          List.length args = 7) (lhs replay_eq) in
      let _,replay_args = strip_comb replay_app in
      let hints = List.nth replay_args 5 in
      let remaining = rand(rhs replay_eq) in
      let stack =
        try rand (find_term
          (fun tm -> is_comb tm && is_const (rator tm) &&
             fst(dest_const(rator tm)) = "set_of_list") goal)
        with Failure _ ->
          failwith "candle_tame_match_replay_ih_tac: missing frontier" in
      MATCH_MP_TAC
        (ISPECL [hints; stack; remaining] replay_ih)));;

let candle_tame_named_condition_cases_tac function_name =
  W (fun (_,goal) ->
    let condition =
      try find_term
        (fun tm ->
          let head,args = strip_comb tm in
          is_var head && fst(dest_var head) = function_name &&
          not (args = []) && type_of tm = `:bool`) goal
      with Failure _ ->
        failwith
          ("candle_tame_named_condition_cases_tac: missing " ^
           function_name) in
    ASM_CASES_TAC condition THEN ASM_REWRITE_TAC[]);;

let candle_tame_match_expansion_frontier_tac frontier_theorem =
  W (fun (assumptions,goal) ->
    let left,right = dest_conj goal in
    let covers,left_args = strip_comb left in
    let _,right_args = strip_comb right in
    let plane_step = List.nth left_args 0 in
    let final = List.nth left_args 1 in
    let tame = List.nth left_args 2 in
    let archived = List.nth left_args 3 in
    let singleton = List.nth left_args 4 in
    let _,singleton_args = strip_comb singleton in
    let state = List.hd singleton_args in
    let rest_set = List.nth right_args 4 in
    let rest = rand rest_set in
    let completion =
      try tryfind
        (find_term (fun tm ->
          let head,args = strip_comb tm in
          is_const head &&
          fst(dest_const head) = "candle_tame_completion_preserved" &&
          List.length args = 5))
        (List.map (fun (_,th) -> concl th) assumptions)
      with Failure _ ->
        failwith
          "candle_tame_match_expansion_frontier_tac: missing completion premise" in
    let _,completion_args = strip_comb completion in
    let invariant = List.nth completion_args 3 in
    let expand = List.nth completion_args 4 in
    MATCH_MP_TAC
      (ISPECL [plane_step; final; tame; archived; invariant; expand;
               state; rest] frontier_theorem));;

let candle_tame_match_final_rejected_tac rejected_theorem =
  W (fun (assumptions,goal) ->
    let _,covers_args = strip_comb goal in
    let plane_step = List.nth covers_args 0 in
    let final = List.nth covers_args 1 in
    let tame = List.nth covers_args 2 in
    let archived = List.nth covers_args 3 in
    let singleton = List.nth covers_args 4 in
    let _,singleton_args = strip_comb singleton in
    let state = List.hd singleton_args in
    let rejection_sound =
      try tryfind
        (fun assumption ->
          let th = snd assumption in
          let _,body = strip_forall (concl th) in
          if is_imp body && is_neg (snd (dest_imp body)) then assumption
          else failwith "not rejection premise") assumptions
      with Failure _ ->
        failwith
          "candle_tame_match_final_rejected_tac: missing rejection premise" in
    let _,rejection_body = strip_forall (concl (snd rejection_sound)) in
    let rejection_antecedent,_ = dest_imp rejection_body in
    let invariant_app,rejection_rest = dest_conj rejection_antecedent in
    let _,reject_app = dest_conj rejection_rest in
    let invariant = rator invariant_app in
    let reject = rator reject_app in
    MATCH_MP_TAC
      (ISPECL [plane_step; final; tame; archived; invariant; reject; state]
        rejected_theorem));;

module Candle_tame_graph_covers_core = struct

(* A list-valued transition is interpreted through ordinary reflexive         *)
(* transitive closure.  This is the typed form of Flyspeck's [RTranCl].        *)

let candle_tame_reaches_def = new_definition
 `candle_tame_reaches (step:A->A list) start finish <=>
    RTC (\x y. MEM y (step x)) start finish`;;

(* [archived g] abstracts the exact production conclusion                     *)
(* [?a. MEM a archive /\ iso_fgraph (fgraph g) a].                           *)

let candle_tame_covers_def = new_definition
 `candle_tame_covers (plane_step:A->A list) final tame archived states <=>
    !s g.
      s IN states /\ candle_tame_reaches plane_step s g /\
      final g /\ tame g
      ==> archived g`;;

let candle_tame_covers_empty = prove
 (`!plane_step final tame archived.
     candle_tame_covers plane_step final tame archived {}`,
  REWRITE_TAC[candle_tame_covers_def; NOT_IN_EMPTY]);;

let candle_tame_covers_union = prove
 (`!plane_step final tame archived left right.
     candle_tame_covers plane_step final tame archived (left UNION right) <=>
     candle_tame_covers plane_step final tame archived left /\
     candle_tame_covers plane_step final tame archived right`,
  REWRITE_TAC[candle_tame_covers_def; IN_UNION] THEN MESON_TAC[]);;

let candle_tame_covers_insert = prove
 (`!plane_step final tame archived state states.
     candle_tame_covers plane_step final tame archived (state INSERT states)
     <=>
     candle_tame_covers plane_step final tame archived {state} /\
     candle_tame_covers plane_step final tame archived states`,
  REWRITE_TAC[candle_tame_covers_def; IN_INSERT; IN_SING] THEN
  MESON_TAC[]);;

let candle_tame_reaches_terminal = prove
 (`!plane_step final s g.
     (!x. final x ==> plane_step x = []) /\ final s /\
     candle_tame_reaches plane_step s g
     ==> g = s`,
  REWRITE_TAC[candle_tame_reaches_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th ->
    let terminal,rest = CONJ_PAIR th in
    let final_state,reach = CONJ_PAIR rest in
    let state = rand (concl final_state) in
    ASSUME_TAC (MATCH_MP (SPEC state terminal) final_state) THEN
    MP_TAC reach) THEN
  ONCE_REWRITE_TAC[RTC_CASES_R] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
   [REFL_TAC;
    ASM_REWRITE_TAC[MEM]]);;

let candle_tame_covers_final_matched = prove
 (`!plane_step final tame archived state.
     (!x. final x ==> plane_step x = []) /\
     final state /\ archived state
     ==> candle_tame_covers plane_step final tame archived {state}`,
  REWRITE_TAC[candle_tame_covers_def; IN_SING] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun outer ->
    let terminal,rest = CONJ_PAIR outer in
    let final_state,archived_state = CONJ_PAIR rest in
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun inner ->
      let start_eq,rest = CONJ_PAIR inner in
      let reach,rest = CONJ_PAIR rest in
      let reach_state = SUBS [start_eq] reach in
      let finish = rand (concl reach_state) in
      let reach_head = rator (concl reach_state) in
      let start = rand reach_head in
      let step = rand (rator reach_head) in
      let final = rator (concl final_state) in
      let terminal_finish = MATCH_MP
        (ISPECL [step;final;start;finish] candle_tame_reaches_terminal)
        (CONJ terminal (CONJ final_state reach_state)) in
      ASSUME_TAC archived_state THEN
      ASSUME_TAC terminal_finish THEN
      ASM_REWRITE_TAC[])));;

let candle_tame_covers_final_rejected = prove
 (`!plane_step final tame archived invariant reject state.
     (!x. final x ==> plane_step x = []) /\
     (!x. invariant x /\ final x /\ reject x ==> ~(tame x)) /\
     invariant state /\ final state /\ reject state
     ==> candle_tame_covers plane_step final tame archived {state}`,
  REWRITE_TAC[candle_tame_covers_def; IN_SING] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun outer ->
    let terminal,rest = CONJ_PAIR outer in
    let reject_sound,rest = CONJ_PAIR rest in
    let inv_state,rest = CONJ_PAIR rest in
    let final_state,reject_state = CONJ_PAIR rest in
    REPEAT GEN_TAC THEN
    DISCH_THEN(fun inner ->
      let start_eq,rest = CONJ_PAIR inner in
      let reach,rest = CONJ_PAIR rest in
      let final_finish,tame_finish = CONJ_PAIR rest in
      let reach_state = SUBS [start_eq] reach in
      let finish = rand (concl reach_state) in
      let reach_head = rator (concl reach_state) in
      let start = rand reach_head in
      let step = rand (rator reach_head) in
      let final = rator (concl final_state) in
      let terminal_finish = MATCH_MP
        (ISPECL [step;final;start;finish] candle_tame_reaches_terminal)
        (CONJ terminal (CONJ final_state reach_state)) in
      let state = rand (concl final_state) in
      let rejected = MATCH_MP (SPEC state reject_sound)
        (CONJ inv_state (CONJ final_state reject_state)) in
      ASSUME_TAC (SUBS [terminal_finish] tame_finish) THEN
      MP_TAC rejected THEN ASM_REWRITE_TAC[])));;

(* These predicates name the two proof obligations that must not be hidden by *)
(* replay.  The start stack must satisfy [invariant]; expansion preserves it;  *)
(* and every tame final completion of an expanded state must route through an *)
(* exact retained successor.                                                   *)

let candle_tame_start_valid_def = new_definition
 `candle_tame_start_valid (invariant:A->bool) starts <=>
    ALL invariant starts`;;

let candle_tame_invariant_preserved_def = new_definition
 `candle_tame_invariant_preserved (invariant:A->bool) expand <=>
    !state child.
      invariant state /\ MEM child (expand state) ==> invariant child`;;

let candle_tame_completion_preserved_def = new_definition
 `candle_tame_completion_preserved
    (plane_step:A->A list) final tame invariant expand <=>
    !state g.
      invariant state /\ ~(final state) /\
      candle_tame_reaches plane_step state g /\ final g /\ tame g
      ==> ?child.
            MEM child (expand state) /\
            candle_tame_reaches plane_step child g`;;

let candle_tame_start_valid_append = prove
 (`!invariant left right:A list.
     candle_tame_start_valid invariant (APPEND left right) <=>
     candle_tame_start_valid invariant left /\
     candle_tame_start_valid invariant right`,
  REWRITE_TAC[candle_tame_start_valid_def; ALL_APPEND]);;

let candle_tame_preserved_children_valid = prove
 (`!invariant expand state:A rest.
     candle_tame_invariant_preserved invariant expand /\
     invariant state /\ candle_tame_start_valid invariant rest
     ==> candle_tame_start_valid invariant (APPEND (expand state) rest)`,
  REWRITE_TAC[candle_tame_invariant_preserved_def;
              candle_tame_start_valid_def; ALL_APPEND; GSYM ALL_MEM] THEN
  MESON_TAC[]);;

let candle_tame_covers_expanded = prove
 (`!plane_step final tame archived invariant expand state.
     candle_tame_completion_preserved
       plane_step final tame invariant expand /\
     invariant state /\ ~(final state) /\
     candle_tame_covers plane_step final tame archived
       (set_of_list (expand state))
     ==> candle_tame_covers plane_step final tame archived {state}`,
  REWRITE_TAC[candle_tame_completion_preserved_def;
              candle_tame_covers_def; IN_SING; IN_SET_OF_LIST] THEN
  MESON_TAC[]);;

(* Reachability is the first invariant that every authentic production replay *)
(* must carry.  It is intentionally kept separate from the much stronger AFP  *)
(* structural invariant: the latter remains an explicit replay premise below.  *)

let candle_tame_reachable_invariant_def = new_definition
 `candle_tame_reachable_invariant
    (step:A->A list) seed state <=>
    candle_tame_reaches step seed state`;;

let candle_tame_reachable_invariant_seed = prove
 (`!step:A->A list seed.
     candle_tame_reachable_invariant step seed seed`,
  REWRITE_TAC[candle_tame_reachable_invariant_def;
              candle_tame_reaches_def; RTC_REFL]);;

let candle_tame_reachable_invariant_step = prove
 (`!step:A->A list seed state child.
     candle_tame_reachable_invariant step seed state /\
     MEM child (step state)
     ==> candle_tame_reachable_invariant step seed child`,
  REWRITE_TAC[candle_tame_reachable_invariant_def;
              candle_tame_reaches_def] THEN
  MESON_TAC[RTC_TRANS_L]);;

(* This conjunction records the general preservation route needed for the AFP *)
(* port: reachability is automatic, while [structural] needs Seed validity and  *)
(* a concrete preservation proof for every retained production successor.       *)

let candle_tame_replay_invariant_def = new_definition
 `candle_tame_replay_invariant
    (step:A->A list) seed structural state <=>
    structural state /\
    candle_tame_reachable_invariant step seed state`;;

let candle_tame_replay_invariant_seed = prove
 (`!step:A->A list seed structural.
     structural seed
     ==> candle_tame_replay_invariant step seed structural seed`,
  REWRITE_TAC[candle_tame_replay_invariant_def;
              candle_tame_reachable_invariant_seed]);;

let candle_tame_replay_invariant_step = prove
 (`!step:A->A list seed structural state child.
     (!parent child.
        structural parent /\
        MEM child (step parent)
        ==> structural child) /\
     candle_tame_replay_invariant step seed structural state /\
     MEM child (step state)
     ==> candle_tame_replay_invariant step seed structural child`,
  REWRITE_TAC[candle_tame_replay_invariant_def] THEN
  MESON_TAC[candle_tame_reachable_invariant_step]);;

(* Production replay normally expands a filtered successor list rather than *)
(* every [plane_step] successor.  These two premises are the exact bridge:   *)
(* the retained children preserve the structural invariant, and each retained*)
(* child is an authentic plane successor.  Thus seed validity plus this one   *)
(* theorem discharges [candle_tame_start_valid] for every replay frontier.     *)

let candle_tame_replay_invariant_preserved = prove
 (`!plane_step:A->A list seed structural expand.
     (!parent child.
        structural parent /\ MEM child (expand parent)
        ==> structural child) /\
     (!parent child.
        MEM child (expand parent) ==> MEM child (plane_step parent))
     ==>
     candle_tame_invariant_preserved
       (candle_tame_replay_invariant plane_step seed structural) expand`,
  REWRITE_TAC[candle_tame_invariant_preserved_def;
              candle_tame_replay_invariant_def] THEN
  MESON_TAC[candle_tame_reachable_invariant_step]);;

(* Frontier lemmas avoid re-proving set algebra inside the replay induction.    *)
(* Their conclusions are exactly the two goals produced by one application of  *)
(* [candle_tame_covers_insert].                                                  *)

let candle_tame_covers_expansion_frontier = prove
 (`!plane_step final tame archived invariant expand state rest.
     candle_tame_completion_preserved
       plane_step final tame invariant expand /\
     invariant state /\
     ~(final state) /\
     candle_tame_covers plane_step final tame archived
       (set_of_list (APPEND (expand state) rest))
     ==>
     candle_tame_covers plane_step final tame archived {state} /\
     candle_tame_covers plane_step final tame archived (set_of_list rest)`,
  REWRITE_TAC[SET_OF_LIST_APPEND; candle_tame_covers_union] THEN
  MESON_TAC[candle_tame_covers_expanded]);;

(* Deterministic depth-first replay.  Hints are consumed only at final states *)
(* not rejected by the executable refutation.  Fuel exhaustion, a missing     *)
(* hint, or a failed leaf check returns [NONE].                                *)

let candle_tame_replay_def = new_recursive_definition num_RECURSION
 `(candle_tame_replay
     (expand:A->A list) final reject (leaf_ok:A->B->bool)
     0 (hints:B list) stack = NONE) /\
  (candle_tame_replay expand final reject leaf_ok
     (SUC fuel) hints stack =
     if stack = [] then SOME hints
     else
       let state = HD stack in
       let rest = TL stack in
       if final state then
         if reject state then
           candle_tame_replay expand final reject leaf_ok fuel hints rest
         else if hints = [] then NONE
         else if leaf_ok state (HD hints) then
           candle_tame_replay expand final reject leaf_ok fuel
             (TL hints) rest
         else NONE
       else
         candle_tame_replay expand final reject leaf_ok fuel hints
           (APPEND (expand state) rest))`;;

(* HOL quotations containing a schematic type can denote a fresh, same-named   *)
(* variable rather than the variable in the current goal.  The goal-driven ML  *)
(* helpers extract exact terms before specializing list cases and polymorphic   *)
(* lemmas.  All resulting proof objects are still checked by the HOL kernel.    *)

(* The theorem deliberately exposes five independent requirements: terminal  *)
(* plane states have no successors; rejection refutes tame final states; a    *)
(* leaf hint establishes the archive property; expansion preserves the state  *)
(* invariant; and pruning preserves every tame final completion.              *)

let candle_tame_replay_sound = prove
 (`!plane_step final tame archived invariant expand reject leaf_ok.
     (!state. final state ==> plane_step state = []) /\
     (!state.
        invariant state /\ final state /\ reject state ==> ~(tame state)) /\
     (!state hint.
        invariant state /\ final state /\ ~(reject state) /\
        leaf_ok state hint
        ==> archived state) /\
     candle_tame_invariant_preserved invariant expand /\
     candle_tame_completion_preserved
       plane_step final tame invariant expand
     ==>
     !fuel hints stack remaining.
       candle_tame_start_valid invariant stack /\
       candle_tame_replay expand final reject leaf_ok
         fuel hints stack = SOME remaining
       ==> candle_tame_covers plane_step final tame archived
             (set_of_list stack)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[candle_tame_replay_def; distinctness "option"];
    ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "replay_ih") THEN
  REPEAT GEN_TAC THEN
  candle_tame_list_cases_tac "stack" "head" "tail" THENL
   [REWRITE_TAC[candle_tame_replay_def; set_of_list;
                candle_tame_covers_empty];
    ALL_TAC] THEN
  REWRITE_TAC[candle_tame_replay_def; NOT_CONS_NIL; HD; TL;
              LET_DEF; LET_END_DEF] THEN
  candle_tame_named_condition_cases_tac "final" THENL
   [candle_tame_named_condition_cases_tac "reject" THENL
     [REWRITE_TAC[candle_tame_start_valid_def; ALL] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[set_of_list] THEN
      ONCE_REWRITE_TAC[candle_tame_covers_insert] THEN
      CONJ_TAC THENL
       [candle_tame_match_final_rejected_tac
          candle_tame_covers_final_rejected THEN
        ASM_REWRITE_TAC[];
        candle_tame_match_replay_ih_tac "replay_ih" THEN
        ASM_REWRITE_TAC[candle_tame_start_valid_def]];
      candle_tame_list_cases_tac "hints" "hint" "hint_tail" THENL
       [REWRITE_TAC[distinctness "option"];
        ALL_TAC] THEN
      REWRITE_TAC[HD; TL; NOT_CONS_NIL] THEN
      candle_tame_named_condition_cases_tac "leaf_ok" THENL
       [REWRITE_TAC[candle_tame_start_valid_def; ALL] THEN STRIP_TAC THEN
        ONCE_REWRITE_TAC[set_of_list] THEN
        ONCE_REWRITE_TAC[candle_tame_covers_insert] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC candle_tame_covers_final_matched THEN
          ASM_MESON_TAC[];
          candle_tame_match_replay_ih_tac "replay_ih" THEN
          ASM_REWRITE_TAC[candle_tame_start_valid_def]];
        REWRITE_TAC[distinctness "option"]]];
    REWRITE_TAC[candle_tame_start_valid_def; ALL] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[set_of_list] THEN
    ONCE_REWRITE_TAC[candle_tame_covers_insert] THEN
    candle_tame_match_expansion_frontier_tac
      candle_tame_covers_expansion_frontier THEN
    ASM_REWRITE_TAC[] THEN
    candle_tame_match_replay_ih_tac "replay_ih" THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC candle_tame_preserved_children_valid THEN
      ASM_REWRITE_TAC[candle_tame_start_valid_def];
      ASM_REWRITE_TAC[]]]);;

end;;

print_endline "CANDLE_TAME_GRAPH_COVERS_CORE_OK DEVELOPMENT_NON_RELEASE";;
