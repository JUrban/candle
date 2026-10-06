(* ========================================================================== *)
(* Late-load adapter from the replay skeleton to Flyspeck tame-graph constants. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Load this only after the ordinary Flyspeck      *)
(* actions containing [Tame_defs], [Tame_defs2], [Tame_list], and              *)
(* [Import_tame_classification].  It does not claim the still-missing AFP      *)
(* structural invariant or the stronger notame7/completion theorem.           *)
(* ========================================================================== *)

needs "candle/tame_graph_covers_core.ml";;

module Candle_tame_graph_covers_production = struct

open Candle_tame_graph_covers_core;;
open Tame_defs;;
open Tame_defs2;;
open Tame_list;;
open Import_tame_classification;;

(* Exact production specialization of the automatic reachability component. *)

let candle_tame_plane_reachable_inv_def = new_definition
 `candle_tame_plane_reachable_inv p graph <=>
    candle_tame_reachable_invariant (next_plane p) (Seed p) graph`;;

let candle_tame_plane_reachable_inv_seed = prove
 (`!p. candle_tame_plane_reachable_inv p (Seed p)`,
  REWRITE_TAC[candle_tame_plane_reachable_inv_def;
              candle_tame_reachable_invariant_seed]);;

let candle_tame_plane_reachable_inv_step = prove
 (`!p graph child.
     candle_tame_plane_reachable_inv p graph /\
     MEM child (next_plane p graph)
     ==> candle_tame_plane_reachable_inv p child`,
  REWRITE_TAC[candle_tame_plane_reachable_inv_def] THEN
  MESON_TAC[candle_tame_reachable_invariant_step]);;

let candle_tame_plane_reachable_inv_rtrancl = prove
 (`!p graph.
     candle_tame_plane_reachable_inv p graph <=>
     (Seed p,graph) IN RTranCl (next_plane p)`,
  REWRITE_TAC[candle_tame_plane_reachable_inv_def;
              candle_tame_reachable_invariant_def;
              candle_tame_reaches_def; RTranCl; IN; UNCURRY_DEF]);;

(* A concrete Seed property, deliberately proved before any large replay.  It *)
(* shows that the authentic initial graph enters the expansion path: its       *)
(* reverse boundary face is nonfinal, so [finalGraph (Seed p)] is false.       *)

let candle_tame_seed_not_final = prove
 (`!p. ~(finalGraph (Seed p))`,
  REWRITE_TAC[finalGraph; nonFinals; SEED; graphl; LET_THM;
              faces_graph; FILTER; SND; NOT_CONS_NIL]);;

(* Exact first-stage executable pruning predicate.  This is the HOL analogue *)
(* of AFP [notame], whose positive inner test is [tame10ub /\ tame11b].  It   *)
(* certifies only that this rejection implies [~tame]; routing every tame     *)
(* completion through stronger retained successors remains an open theorem.   *)

let candle_tame_notame_def = new_definition
 `candle_tame_notame g <=>
    ~(countVertices g <= 15 /\ tame11b g)`;;

let candle_tame_notame_sound = prove
 (`!g. candle_tame_notame g ==> ~(tame g)`,
  REWRITE_TAC[candle_tame_notame_def; tame; tame10; LET_THM] THEN
  MESON_TAC[]);;

end;;

print_endline
  "CANDLE_TAME_GRAPH_COVERS_PRODUCTION_OK DEVELOPMENT_NON_RELEASE";;
