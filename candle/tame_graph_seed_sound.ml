(* ========================================================================== *)
(* Seed-specialized entry point for deterministic tame-graph replay.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This corollary makes the starting invariant    *)
(* explicit and discharges it from seed validity and general preservation.    *)
(* ========================================================================== *)

needs "candle/tame_graph_covers_core.ml";;

(* The hint type is intentionally schematic.  Extract the exact replay terms *)
(* from the live goal instead of inventing a same-named fresh type variable.   *)

let candle_tame_seed_apply_replay_sound_tac =
  W (fun (assumptions,goal) ->
    let covers_head,covers_args = strip_comb goal in
    if not (is_const covers_head &&
            fst(dest_const covers_head) = "candle_tame_covers") then
      failwith "candle_tame_seed_apply_replay_sound_tac: covers goal"
    else
      let plane_step = List.nth covers_args 0 in
      let final = List.nth covers_args 1 in
      let tame = List.nth covers_args 2 in
      let archived = List.nth covers_args 3 in
      let replay_eq =
        try tryfind
          (find_term (fun tm -> is_eq tm &&
             can (find_term (fun subtm ->
               let head,args = strip_comb subtm in
               is_const head &&
               fst(dest_const head) = "candle_tame_replay" &&
               List.length args = 7)) (lhs tm)))
          (List.map (fun (_,th) -> concl th) assumptions)
        with Failure _ ->
          failwith "candle_tame_seed_apply_replay_sound_tac: replay result" in
      let replay_app = find_term
        (fun tm ->
          let head,args = strip_comb tm in
          is_const head &&
          fst(dest_const head) = "candle_tame_replay" &&
          List.length args = 7) (lhs replay_eq) in
      let _,replay_args = strip_comb replay_app in
      let expand = List.nth replay_args 0 in
      let reject = List.nth replay_args 2 in
      let leaf_ok = List.nth replay_args 3 in
      let completion_app =
        try tryfind
          (fun (_,th) ->
            let head,args = strip_comb (concl th) in
            if is_const head &&
               fst(dest_const head) = "candle_tame_completion_preserved" &&
               List.length args = 5 then concl th
            else failwith "not completion premise")
          assumptions
        with Failure _ ->
          failwith "candle_tame_seed_apply_replay_sound_tac: completion" in
      let _,completion_args = strip_comb completion_app in
      let invariant = List.nth completion_args 3 in
      let completion_expand = List.nth completion_args 4 in
      if not (aconv completion_expand expand) then
        failwith "candle_tame_seed_apply_replay_sound_tac: expansion mismatch"
      else
      let invariant_head,invariant_args = strip_comb invariant in
      if not (is_const invariant_head &&
              fst(dest_const invariant_head) =
                "candle_tame_replay_invariant" &&
              List.length invariant_args = 3) then
        failwith "candle_tame_seed_apply_replay_sound_tac: replay invariant"
      else
      let invariant_step = List.nth invariant_args 0 in
      let seed = List.nth invariant_args 1 in
      let structural = List.nth invariant_args 2 in
      if not (aconv invariant_step plane_step) then
        failwith "candle_tame_seed_apply_replay_sound_tac: step mismatch"
      else
      let rec prove_from assumptions tm =
        try snd (tryfind
          (fun assumption ->
            if aconv (concl (snd assumption)) tm then assumption
            else failwith "different assumption") assumptions)
        with Failure _ ->
          let left,right = dest_conj tm in
          CONJ (prove_from assumptions left)
               (prove_from assumptions right) in
      let invariant_preserved_base =
        ISPEC expand
         (ISPEC structural
          (ISPEC seed
           (ISPEC plane_step
             Candle_tame_graph_covers_core.
               candle_tame_replay_invariant_preserved))) in
      let invariant_preserved_premise,_ =
        dest_imp (concl invariant_preserved_base) in
      let invariant_preserved =
        MP invariant_preserved_base
          (prove_from assumptions invariant_preserved_premise) in
      let seed_invariant_base =
        ISPEC structural
         (ISPEC seed
          (ISPEC plane_step
            Candle_tame_graph_covers_core.candle_tame_replay_invariant_seed)) in
      let seed_invariant_premise,_ = dest_imp (concl seed_invariant_base) in
      let seed_invariant =
        MP seed_invariant_base
          (prove_from assumptions seed_invariant_premise) in
      let fuel = List.nth replay_args 4 in
      let hints = List.nth replay_args 5 in
      let stack = List.nth replay_args 6 in
      let start_valid_equivalence =
        REWRITE_RULE[ALL]
          (ISPEC stack
           (ISPEC invariant
             Candle_tame_graph_covers_core.candle_tame_start_valid_def)) in
      let _,seed_implies_start_valid =
        EQ_IMP_RULE start_valid_equivalence in
      let start_valid = MP seed_implies_start_valid seed_invariant in
      let assumptions =
        ("candle_tame_invariant_preserved",invariant_preserved) ::
        ("candle_tame_start_valid",start_valid) :: assumptions in
      let replay_sound =
        ISPEC leaf_ok
         (ISPEC reject
          (ISPEC expand
           (ISPEC invariant
            (ISPEC archived
             (ISPEC tame
              (ISPEC final
               (ISPEC plane_step
                 Candle_tame_graph_covers_core.candle_tame_replay_sound))))))) in
      let general_premise,_ = dest_imp (concl replay_sound) in
      let replay_sound =
        MP replay_sound (prove_from assumptions general_premise) in
      let remaining = rand (rhs replay_eq) in
      let replay_sound =
        ISPEC remaining
         (ISPEC stack
          (ISPEC hints
           (ISPEC fuel replay_sound))) in
      let run_premise,_ = dest_imp (concl replay_sound) in
      let result =
        MP replay_sound (prove_from assumptions run_premise) in
      if aconv (concl result) goal then ACCEPT_TAC result
      else failwith "candle_tame_seed_apply_replay_sound_tac: conclusion");;

module Candle_tame_graph_seed_sound = struct

open Candle_tame_graph_covers_core;;

let candle_tame_seed_replay_sound = prove
 (`!plane_step:A->A list final tame archived structural expand reject leaf_ok
     seed.
     (!state. final state ==> plane_step state = []) /\
     (!state.
        candle_tame_replay_invariant plane_step seed structural state /\
        final state /\ reject state
        ==> ~(tame state)) /\
     (!state hint.
        candle_tame_replay_invariant plane_step seed structural state /\
        final state /\ ~(reject state) /\ leaf_ok state hint
        ==> archived state) /\
     structural seed /\
     (!parent child.
        structural parent /\ MEM child (expand parent)
        ==> structural child) /\
     (!parent child.
        MEM child (expand parent) ==> MEM child (plane_step parent)) /\
     candle_tame_completion_preserved
       plane_step final tame
       (candle_tame_replay_invariant plane_step seed structural) expand
     ==>
     !fuel hints remaining.
       candle_tame_replay expand final reject leaf_ok
         fuel hints [seed] = SOME remaining
       ==> candle_tame_covers plane_step final tame archived
             (set_of_list [seed])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  candle_tame_seed_apply_replay_sound_tac);;

end;;

print_endline
  "CANDLE_TAME_GRAPH_SEED_SOUND_OK DEVELOPMENT_NON_RELEASE";;
