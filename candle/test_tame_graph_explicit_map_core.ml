(* Fresh-base kernel checks for the source-independent explicit-map core. *)

let candle_tame_explicit_map_core_axioms_before = axioms ();;

needs "candle/tame_graph_explicit_map_core.ml";;

open Candle_tame_graph_explicit_map_core;;

let candle_tame_explicit_map_core_theorems =
 [candle_tame_list_distinct_map_injective;
  candle_tame_vertex_map_apply_pair_member;
  candle_tame_vertex_map_apply_injective_on_vertices;
  candle_tame_fgraph_vertices_set;
  candle_tame_explicit_map_shape_injective];;

if not (List.for_all (fun theorem -> hyp theorem = [])
          candle_tame_explicit_map_core_theorems) then
  failwith "tame explicit map core: theorem has assumptions";;

let candle_tame_explicit_map_core_axioms_after = axioms ();;

if length candle_tame_explicit_map_core_axioms_after <>
     length candle_tame_explicit_map_core_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_tame_explicit_map_core_axioms_before)
     candle_tame_explicit_map_core_axioms_after) then
  failwith "tame explicit map core: changed the global axiom set";;

let _ = print_endline
  "CANDLE_TAME_GRAPH_EXPLICIT_MAP_CORE_TEST_OK assumptions=0 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
