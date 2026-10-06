(* Fresh-base kernel checks for the tame-graph coverage/replay skeleton. *)

let candle_tame_covers_axioms_before = axioms ();;

needs "candle/tame_graph_covers_core.ml";;

open Candle_tame_graph_covers_core;;

let candle_tame_covers_checked_theorems =
 [candle_tame_covers_empty;
  candle_tame_covers_union;
  candle_tame_covers_insert;
  candle_tame_reaches_terminal;
  candle_tame_covers_final_matched;
  candle_tame_covers_final_rejected;
  candle_tame_start_valid_append;
  candle_tame_preserved_children_valid;
  candle_tame_covers_expanded;
  candle_tame_reachable_invariant_seed;
  candle_tame_reachable_invariant_step;
  candle_tame_replay_invariant_seed;
  candle_tame_replay_invariant_step;
  candle_tame_covers_expansion_frontier;
  candle_tame_replay_sound];;

if not (List.for_all (fun theorem -> hyp theorem = [])
          candle_tame_covers_checked_theorems) then
  failwith "tame graph covers core: theorem has assumptions";;

let candle_tame_covers_axioms_after = axioms ();;

if length candle_tame_covers_axioms_after <>
     length candle_tame_covers_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_tame_covers_axioms_before)
     candle_tame_covers_axioms_after) then
  failwith "tame graph covers core: changed the global axiom set";;

print_endline
  "CANDLE_TAME_GRAPH_COVERS_CORE_TEST_OK assumptions=0 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
