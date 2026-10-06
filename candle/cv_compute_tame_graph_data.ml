(* ========================================================================== *)
(* Reflected data boundary for the Flyspeck tame-graph checker.               *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This file establishes only the typed,          *)
(* fail-closed representation layer.  It does not claim archive completeness  *)
(* or connect the executable checks to Flyspeck's production [iso_fgraph].     *)
(* ========================================================================== *)

needs "candle/compute.ml";;
needs "candle/cv_compute_flyspeck_lists_core.ml";;

module Candle_cv_tame_graph_data = struct

open Candle_cv_flyspeck_lists_core;;

(* A face is a list of vertex numbers, an fgraph is a list of faces, and an   *)
(* explicit vertex map is a list of source/target pairs.  The encoders below  *)
(* reuse the common cval list convention: [Cexp_num 0] is nil and             *)
(* [Cexp_pair h t] is cons.                                                    *)

let candle_cv_tame_face_def = new_definition
 `candle_cv_tame_face (face:num list) = candle_cv_num_list face`;;

let candle_cv_tame_fgraph_def = new_definition
 `candle_cv_tame_fgraph (graph:(num list)list) = candle_cv_num_lists graph`;;

let candle_cv_tame_vertex_map_def = new_definition
 `candle_cv_tame_vertex_map (mapping:(num#num)list) =
    candle_cv_num_pair_list mapping`;;

let candle_cv_tame_face_decode_def = define
 `(candle_cv_tame_face_decode (Cexp_num n) = ([]:num list)) /\
  (candle_cv_tame_face_decode (Cexp_pair h t) =
     CONS (candle_cv_num_decode h) (candle_cv_tame_face_decode t))`;;

let candle_cv_tame_fgraph_decode_def = define
 `(candle_cv_tame_fgraph_decode (Cexp_num n) = ([]:(num list)list)) /\
  (candle_cv_tame_fgraph_decode (Cexp_pair h t) =
     CONS (candle_cv_tame_face_decode h)
          (candle_cv_tame_fgraph_decode t))`;;

let candle_cv_tame_face_roundtrip = prove
 (`!face:num list.
     candle_cv_tame_face_decode (candle_cv_tame_face face) = face`,
  REWRITE_TAC[candle_cv_tame_face_def] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_list_def;
                  candle_cv_tame_face_decode_def;
                  candle_cv_num_decode_def]);;

let candle_cv_tame_fgraph_roundtrip = prove
 (`!graph:(num list)list.
     candle_cv_tame_fgraph_decode (candle_cv_tame_fgraph graph) = graph`,
  REWRITE_TAC[candle_cv_tame_fgraph_def] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_lists_def;
                  candle_cv_tame_fgraph_decode_def;
                  GSYM candle_cv_tame_face_def;
                  candle_cv_tame_face_roundtrip]);;

let candle_cv_tame_vertex_map_roundtrip = prove
 (`!mapping:(num#num)list.
     candle_cv_num_pair_list_decode (candle_cv_tame_vertex_map mapping) =
     mapping`,
  REWRITE_TAC[candle_cv_tame_vertex_map_def;
              candle_cv_num_pair_list_roundtrip]);;

let candle_cv_tame_face_injective = prove
 (`!face1 face2:num list.
     candle_cv_tame_face face1 = candle_cv_tame_face face2 <=> face1 = face2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_tame_face_decode`) THEN
    REWRITE_TAC[candle_cv_tame_face_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_tame_fgraph_injective = prove
 (`!graph1 graph2:(num list)list.
     candle_cv_tame_fgraph graph1 = candle_cv_tame_fgraph graph2 <=>
     graph1 = graph2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN (MP_TAC o AP_TERM `candle_cv_tame_fgraph_decode`) THEN
    REWRITE_TAC[candle_cv_tame_fgraph_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

let candle_cv_tame_vertex_map_injective = prove
 (`!map1 map2:(num#num)list.
     candle_cv_tame_vertex_map map1 = candle_cv_tame_vertex_map map2 <=>
     map1 = map2`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN
      (MP_TAC o AP_TERM `candle_cv_num_pair_list_decode`) THEN
    REWRITE_TAC[candle_cv_tame_vertex_map_roundtrip];
    DISCH_THEN SUBST1_TAC THEN REFL_TAC]);;

(* Strict executable validators.  A nonzero numeric value is not accepted as *)
(* a list terminator, a pair is not accepted as a vertex, and all failure     *)
(* paths return [Cexp_num 0].                                                  *)

let candle_cv_tame_num_member_def = define
 `(candle_cv_tame_num_member needle (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_num_member needle (Cexp_pair h t) =
     Cexp_if (Cexp_eq needle h)
       (Cexp_num 1)
       (candle_cv_tame_num_member needle t))`;;

let candle_cv_tame_num_list_valid_aux_def = define
 `(candle_cv_tame_num_list_valid_aux bound seen (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_tame_num_list_valid_aux bound seen (Cexp_pair h t) =
     Cexp_if (Cexp_ispair h)
       (Cexp_num 0)
       (Cexp_if (Cexp_less h bound)
         (Cexp_if (candle_cv_tame_num_member h seen)
           (Cexp_num 0)
           (candle_cv_tame_num_list_valid_aux
             bound (Cexp_pair h seen) t))
         (Cexp_num 0)))`;;

let candle_cv_tame_num_list_valid_def = new_definition
 `candle_cv_tame_num_list_valid bound values =
    candle_cv_tame_num_list_valid_aux bound (Cexp_num 0) values`;;

let candle_cv_tame_fgraph_valid_def = define
 `(candle_cv_tame_fgraph_valid bound (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_tame_fgraph_valid bound (Cexp_pair face faces) =
     Cexp_if (Cexp_ispair face)
       (Cexp_if (candle_cv_tame_num_list_valid bound face)
         (candle_cv_tame_fgraph_valid bound faces)
         (Cexp_num 0))
       (Cexp_num 0))`;;

let candle_cv_tame_nonempty_fgraph_valid_def = new_definition
 `candle_cv_tame_nonempty_fgraph_valid bound graph =
    Cexp_if (Cexp_ispair graph)
      (candle_cv_tame_fgraph_valid bound graph)
      (Cexp_num 0)`;;

let candle_cv_tame_vertex_map_valid_aux_def = define
 `(candle_cv_tame_vertex_map_valid_aux
     source_bound target_bound seen_sources seen_targets (Cexp_num n) =
     Cexp_eq (Cexp_num n) (Cexp_num 0)) /\
  (candle_cv_tame_vertex_map_valid_aux
     source_bound target_bound seen_sources seen_targets
     (Cexp_pair entry entries) =
     Cexp_if (Cexp_ispair entry)
       (Cexp_if (Cexp_ispair (Cexp_fst entry))
         (Cexp_num 0)
         (Cexp_if (Cexp_ispair (Cexp_snd entry))
           (Cexp_num 0)
           (Cexp_if (Cexp_less (Cexp_fst entry) source_bound)
             (Cexp_if (Cexp_less (Cexp_snd entry) target_bound)
               (Cexp_if
                 (candle_cv_tame_num_member
                   (Cexp_fst entry) seen_sources)
                 (Cexp_num 0)
                 (Cexp_if
                   (candle_cv_tame_num_member
                     (Cexp_snd entry) seen_targets)
                   (Cexp_num 0)
                   (candle_cv_tame_vertex_map_valid_aux
                     source_bound target_bound
                     (Cexp_pair (Cexp_fst entry) seen_sources)
                     (Cexp_pair (Cexp_snd entry) seen_targets)
                     entries)))
               (Cexp_num 0))
             (Cexp_num 0))))
       (Cexp_num 0))`;;

let candle_cv_tame_vertex_map_valid_def = new_definition
 `candle_cv_tame_vertex_map_valid source_bound target_bound mapping =
    candle_cv_tame_vertex_map_valid_aux
      source_bound target_bound (Cexp_num 0) (Cexp_num 0) mapping`;;

(* All-variable equations are the equations admitted to [Kernel.compute].    *)

let candle_cv_tame_num_member_compute = prove
 (`!needle values.
     candle_cv_tame_num_member needle values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq needle (Cexp_fst values))
         (Cexp_num 1)
         (candle_cv_tame_num_member needle (Cexp_snd values)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_num_member_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_num_list_valid_aux_compute = prove
 (`!bound seen values.
     candle_cv_tame_num_list_valid_aux bound seen values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_ispair (Cexp_fst values))
         (Cexp_num 0)
         (Cexp_if (Cexp_less (Cexp_fst values) bound)
           (Cexp_if
             (candle_cv_tame_num_member (Cexp_fst values) seen)
             (Cexp_num 0)
             (candle_cv_tame_num_list_valid_aux
               bound (Cexp_pair (Cexp_fst values) seen)
               (Cexp_snd values)))
           (Cexp_num 0)))
       (Cexp_eq values (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_num_list_valid_aux_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_num_list_valid_compute =
  SPEC_ALL candle_cv_tame_num_list_valid_def;;

let candle_cv_tame_fgraph_valid_compute = prove
 (`!bound graph.
     candle_cv_tame_fgraph_valid bound graph =
     Cexp_if (Cexp_ispair graph)
       (Cexp_if (Cexp_ispair (Cexp_fst graph))
         (Cexp_if
           (candle_cv_tame_num_list_valid bound (Cexp_fst graph))
           (candle_cv_tame_fgraph_valid bound (Cexp_snd graph))
           (Cexp_num 0))
         (Cexp_num 0))
       (Cexp_eq graph (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `graph:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_fgraph_valid_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_nonempty_fgraph_valid_compute =
  SPEC_ALL candle_cv_tame_nonempty_fgraph_valid_def;;

let candle_cv_tame_vertex_map_valid_aux_compute = prove
 (`!source_bound target_bound seen_sources seen_targets mapping.
     candle_cv_tame_vertex_map_valid_aux
       source_bound target_bound seen_sources seen_targets mapping =
     Cexp_if (Cexp_ispair mapping)
       (Cexp_if (Cexp_ispair (Cexp_fst mapping))
         (Cexp_if (Cexp_ispair (Cexp_fst (Cexp_fst mapping)))
           (Cexp_num 0)
           (Cexp_if (Cexp_ispair (Cexp_snd (Cexp_fst mapping)))
             (Cexp_num 0)
             (Cexp_if
               (Cexp_less (Cexp_fst (Cexp_fst mapping)) source_bound)
               (Cexp_if
                 (Cexp_less (Cexp_snd (Cexp_fst mapping)) target_bound)
                 (Cexp_if
                   (candle_cv_tame_num_member
                     (Cexp_fst (Cexp_fst mapping)) seen_sources)
                   (Cexp_num 0)
                   (Cexp_if
                     (candle_cv_tame_num_member
                       (Cexp_snd (Cexp_fst mapping)) seen_targets)
                     (Cexp_num 0)
                     (candle_cv_tame_vertex_map_valid_aux
                       source_bound target_bound
                       (Cexp_pair (Cexp_fst (Cexp_fst mapping))
                         seen_sources)
                       (Cexp_pair (Cexp_snd (Cexp_fst mapping))
                         seen_targets)
                       (Cexp_snd mapping))))
                 (Cexp_num 0))
               (Cexp_num 0))))
         (Cexp_num 0))
       (Cexp_eq mapping (Cexp_num 0))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `mapping:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_vertex_map_valid_aux_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_vertex_map_valid_compute =
  SPEC_ALL candle_cv_tame_vertex_map_valid_def;;

let candle_cv_tame_graph_data_compute_eqs =
  map SPEC_ALL
   [candle_cv_tame_num_member_compute;
    candle_cv_tame_num_list_valid_aux_compute;
    candle_cv_tame_num_list_valid_compute;
    candle_cv_tame_fgraph_valid_compute;
    candle_cv_tame_nonempty_fgraph_valid_compute;
    candle_cv_tame_vertex_map_valid_aux_compute;
    candle_cv_tame_vertex_map_valid_compute];;

let _ =
  print_endline "CANDLE_CV_TAME_GRAPH_DATA_OK DEVELOPMENT_NON_RELEASE";;

end;;
