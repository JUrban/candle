(* ========================================================================== *)
(* Source-independent explicit-map facts for the tame-graph checker.          *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The production [iso_fgraph] bridge is in the  *)
(* late-load module.  This core proves the finite association-list and graph  *)
(* vertex facts without depending on Flyspeck's expensive tame libraries.     *)
(* ========================================================================== *)

module Candle_tame_graph_explicit_map_core = struct

let candle_tame_list_distinct_def = define
 `(candle_tame_list_distinct ([]:A list) <=> T) /\
  (candle_tame_list_distinct (CONS head tail) <=>
     ~(MEM head tail) /\ candle_tame_list_distinct tail)`;;

let candle_tame_list_distinct_map_injective = prove
 (`!f:A->B values.
     candle_tame_list_distinct (MAP f values)
     ==> !x y.
           MEM x values /\ MEM y values /\ f x = f y
           ==> x = y`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; candle_tame_list_distinct_def; MEM];
    ASM_REWRITE_TAC[MAP; candle_tame_list_distinct_def] THEN
    STRIP_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[MEM] THEN
    STRIP_TAC THEN ASM_MESON_TAC[MEM_MAP]]);;

let candle_tame_vertex_map_apply_def =
  new_recursive_definition list_RECURSION
   `(candle_tame_vertex_map_apply default
       ([]:(num#num)list) vertex = default) /\
    (candle_tame_vertex_map_apply default (CONS entry rest) vertex =
       if vertex = FST entry then SND entry
       else candle_tame_vertex_map_apply default rest vertex)`;;

let candle_tame_vertex_map_apply_pair_member = prove
 (`!default mapping vertex.
     MEM vertex (MAP FST mapping)
     ==> MEM
          (vertex,candle_tame_vertex_map_apply default mapping vertex)
          mapping`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; MEM];
    ASM_REWRITE_TAC[MAP; MEM; candle_tame_vertex_map_apply_def] THEN
    GEN_TAC THEN
    ASM_CASES_TAC `vertex = FST (h:num#num)` THEN
    ASM_REWRITE_TAC[PAIR_EQ; FST; SND] THEN ASM_MESON_TAC[]]);;

let candle_tame_injective_on_def = new_definition
 `candle_tame_injective_on f s <=>
    !x y. x IN s /\ y IN s /\ f x = f y ==> x = y`;;

let candle_tame_vertex_map_apply_injective_on_vertices = prove
 (`!default mapping vertices.
     candle_tame_list_distinct (MAP SND mapping) /\
     (!vertex.
        MEM vertex vertices ==> MEM vertex (MAP FST mapping))
     ==>
     candle_tame_injective_on
       (candle_tame_vertex_map_apply default mapping)
       (set_of_list vertices)`,
  REWRITE_TAC[candle_tame_injective_on_def; IN_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL [`SND:num#num->num`; `mapping:(num#num)list`]
      candle_tame_list_distinct_map_injective) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN
    (MP_TAC o SPECL
      [`(x,candle_tame_vertex_map_apply default mapping x):num#num`;
       `(y,candle_tame_vertex_map_apply default mapping y):num#num`]) THEN
  ASM_REWRITE_TAC[FST; SND; PAIR_EQ] THEN
  ASM_MESON_TAC[candle_tame_vertex_map_apply_pair_member]);;

let candle_tame_fgraph_vertices_def = define
 `(candle_tame_fgraph_vertices ([]:(num list)list) = []) /\
  (candle_tame_fgraph_vertices (CONS face faces) =
     APPEND face (candle_tame_fgraph_vertices faces))`;;

let candle_tame_fgraph_vertices_set = prove
 (`!source:(num list)list.
     set_of_list (candle_tame_fgraph_vertices source) =
     UNIONS
       (IMAGE (\face. set_of_list face) (set_of_list source))`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_tame_fgraph_vertices_def; set_of_list;
                  SET_OF_LIST_APPEND; IMAGE_CLAUSES;
                  UNIONS_0; UNIONS_INSERT]);;

let candle_tame_explicit_map_shape_def = new_definition
 `candle_tame_explicit_map_shape
    (mapping:(num#num)list) (source:(num list)list) <=>
    candle_tame_list_distinct (MAP FST mapping) /\
    candle_tame_list_distinct (MAP SND mapping) /\
    (!vertex.
       MEM vertex (candle_tame_fgraph_vertices source)
       ==> MEM vertex (MAP FST mapping))`;;

let candle_tame_explicit_map_shape_injective = prove
 (`!default mapping source.
     candle_tame_explicit_map_shape mapping source
     ==>
     candle_tame_injective_on
       (candle_tame_vertex_map_apply default mapping)
       (UNIONS
         (IMAGE (\face. set_of_list face) (set_of_list source)))`,
  REWRITE_TAC[candle_tame_explicit_map_shape_def] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL
      [`default:num`; `mapping:(num#num)list`;
       `candle_tame_fgraph_vertices source:num list`]
      candle_tame_vertex_map_apply_injective_on_vertices) THEN
  ASM_REWRITE_TAC[candle_tame_fgraph_vertices_set]);;

end;;

let _ = print_endline
  "CANDLE_TAME_GRAPH_EXPLICIT_MAP_CORE_OK DEVELOPMENT_NON_RELEASE";;
