(* ========================================================================== *)
(* Faithful reflected successor construction for the AFP tame enumerator.    *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The definitions below follow Enumerator.thy,  *)
(* Plane.thy, and FaceDivision.thy.  Enumeration tables are authenticated     *)
(* finite input data; duplicate-edge filtering, reification, subdivision,    *)
(* face-list updates, heights, and finalization execute through               *)
(* Kernel.compute.                                                            *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_enumerator_core.ml";;

module Candle_cv_tame_graph_successor = struct

open Candle_cv_tame_graph_enumerator_core;;

let candle_cv_tame_singleton_def = new_definition
 `candle_cv_tame_singleton value = Cexp_pair value (Cexp_num 0)`;;

let candle_cv_tame_some_def = new_definition
 `candle_cv_tame_some value = Cexp_pair value (Cexp_num 0)`;;

let candle_cv_tame_min_num_def = new_definition
 `candle_cv_tame_min_num left right =
    Cexp_if (candle_cv_tame_le left right) left right`;;

(* Isabelle mapAt ns (replace old replacement) tables. *)
let candle_cv_tame_replace_faces_at_def = define
 `(candle_cv_tame_replace_faces_at (Cexp_num n) old replacement tables =
     tables) /\
  (candle_cv_tame_replace_faces_at (Cexp_pair index rest) old replacement
       tables =
     (let current = candle_cv_tame_list_nth (Cexp_num 0) tables index in
      let updated = candle_cv_tame_list_replace old replacement current in
      candle_cv_tame_replace_faces_at rest old replacement
        (candle_cv_tame_list_update tables index updated)))`;;

let candle_cv_tame_map_face_lists_replace_def = define
 `(candle_cv_tame_map_face_lists_replace old replacement (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_tame_map_face_lists_replace old replacement
       (Cexp_pair faces rest) =
     Cexp_pair (candle_cv_tame_list_replace old replacement faces)
       (candle_cv_tame_map_face_lists_replace old replacement rest))`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_replace";;

let candle_cv_tame_make_face_final_def = new_definition
 `candle_cv_tame_make_face_final face graph =
    (let final_face = candle_cv_tame_face_set_final face in
     let replacement = candle_cv_tame_singleton final_face in
     candle_cv_tame_graph
       (candle_cv_tame_list_replace face replacement
         (candle_cv_tame_graph_faces graph))
       (candle_cv_tame_graph_vertex_count graph)
       (candle_cv_tame_map_face_lists_replace face replacement
         (candle_cv_tame_graph_faces_at graph))
       (candle_cv_tame_graph_heights graph))`;;

(* Produce consecutive fresh vertices, driven by one checked list cell for   *)
(* every None encountered.  This avoids adding constructor equations to the  *)
(* fixed Kernel.compute initializer.                                          *)
let candle_cv_tame_fresh_vertices_def = define
 `(candle_cv_tame_fresh_vertices current (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_fresh_vertices current (Cexp_pair token rest) =
     Cexp_pair current
       (candle_cv_tame_fresh_vertices
         (Cexp_add current (Cexp_num 1)) rest))`;;

let candle_cv_tame_heights_new_aux_def = define
 `(candle_cv_tame_heights_new_aux h1 h2 total index (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_tame_heights_new_aux h1 h2 total index
       (Cexp_pair token rest) =
     Cexp_pair
       (candle_cv_tame_min_num
         (Cexp_add h1 (Cexp_add index (Cexp_num 1)))
         (Cexp_add h2 (Cexp_sub total index)))
       (candle_cv_tame_heights_new_aux h1 h2 total
         (Cexp_add index (Cexp_num 1)) rest))`;;

let candle_cv_tame_heights_new_vertices_def = new_definition
 `candle_cv_tame_heights_new_vertices h1 h2 new_vertices =
    candle_cv_tame_heights_new_aux h1 h2
      (candle_cv_tame_list_length new_vertices) (Cexp_num 0) new_vertices`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_heights";;

let candle_cv_tame_split_face_def = new_definition
 `candle_cv_tame_split_face old_face ram1 ram2 new_vertices =
    (let vertices = candle_cv_tame_face_vertices old_face in
     let path1 = Cexp_pair ram1
       (candle_cv_tame_list_append
         (candle_cv_tame_between vertices ram1 ram2)
         (candle_cv_tame_singleton ram2)) in
     let path2 = Cexp_pair ram2
       (candle_cv_tame_list_append
         (candle_cv_tame_between vertices ram2 ram1)
         (candle_cv_tame_singleton ram1)) in
     let face1 = candle_cv_tame_face
       (candle_cv_tame_list_append
         (candle_cv_tame_list_reverse new_vertices) path1)
       candle_cv_tame_false in
     let face2 = candle_cv_tame_face
       (candle_cv_tame_list_append path2 new_vertices)
       candle_cv_tame_false in
     Cexp_pair face1 face2)`;;

(* The outer-list shape of new_vertices is used only as a repeat control. *)
let candle_cv_tame_replicate_face_pair_def = define
 `(candle_cv_tame_replicate_face_pair face_pair (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_replicate_face_pair face_pair (Cexp_pair token rest) =
     Cexp_pair face_pair
       (candle_cv_tame_replicate_face_pair face_pair rest))`;;

(* Correct the deliberately generic map above to the AFP replicate operation. *)
let candle_cv_tame_split_face_graph_exact_def = new_definition
 `candle_cv_tame_split_face_graph_exact graph ram1 ram2 old_face new_vertices =
    (let faces = candle_cv_tame_graph_faces graph in
     let vertex_count = candle_cv_tame_graph_vertex_count graph in
     let faces_at0 = candle_cv_tame_graph_faces_at graph in
     let heights = candle_cv_tame_graph_heights graph in
     let old_vertices = candle_cv_tame_face_vertices old_face in
     let vertices1 = candle_cv_tame_between old_vertices ram1 ram2 in
     let vertices2 = candle_cv_tame_between old_vertices ram2 ram1 in
     let split = candle_cv_tame_split_face old_face ram1 ram2 new_vertices in
     let face1 = Cexp_fst split in
     let face2 = Cexp_snd split in
     let faces_at1 = candle_cv_tame_replace_faces_at vertices1 old_face
       (candle_cv_tame_singleton face1) faces_at0 in
     let faces_at2 = candle_cv_tame_replace_faces_at vertices2 old_face
       (candle_cv_tame_singleton face2) faces_at1 in
     let faces_at3 = candle_cv_tame_replace_faces_at
       (candle_cv_tame_singleton ram1) old_face
       (Cexp_pair face2 (candle_cv_tame_singleton face1)) faces_at2 in
     let faces_at4 = candle_cv_tame_replace_faces_at
       (candle_cv_tame_singleton ram2) old_face
       (Cexp_pair face1 (candle_cv_tame_singleton face2)) faces_at3 in
     let face_pair = Cexp_pair face1 (candle_cv_tame_singleton face2) in
     let faces_at = candle_cv_tame_list_append faces_at4
       (candle_cv_tame_replicate_face_pair face_pair new_vertices) in
     let new_heights = candle_cv_tame_heights_new_vertices
       (candle_cv_tame_graph_height graph ram1)
       (candle_cv_tame_graph_height graph ram2) new_vertices in
     let new_graph = candle_cv_tame_graph
       (candle_cv_tame_list_append
         (candle_cv_tame_list_replace old_face
           (candle_cv_tame_singleton face2) faces)
         (candle_cv_tame_singleton face1))
       (Cexp_add vertex_count (candle_cv_tame_list_length new_vertices))
       faces_at (candle_cv_tame_list_append heights new_heights) in
     Cexp_pair face1 (Cexp_pair face2 new_graph))`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_split";;

(* pending has one list cell for every consecutive None. *)
let candle_cv_tame_subdiv_face_aux_def = define
 `(candle_cv_tame_subdiv_face_aux graph face vertex pending (Cexp_num n) =
     candle_cv_tame_make_face_final face graph) /\
  (candle_cv_tame_subdiv_face_aux graph face vertex pending
       (Cexp_pair option_value rest) =
     Cexp_if (Cexp_ispair option_value)
       (let next = Cexp_fst option_value in
        Cexp_if
          (candle_cv_tame_and
            (Cexp_eq (candle_cv_tame_next_vertex face vertex) next)
            (candle_cv_tame_not (Cexp_ispair pending)))
          (candle_cv_tame_subdiv_face_aux graph face next (Cexp_num 0) rest)
          (let new_vertices = candle_cv_tame_fresh_vertices
             (candle_cv_tame_graph_vertex_count graph) pending in
           let split = candle_cv_tame_split_face_graph_exact
             graph vertex next face new_vertices in
           let face2 = Cexp_fst (Cexp_snd split) in
           let next_graph = Cexp_snd (Cexp_snd split) in
           candle_cv_tame_subdiv_face_aux next_graph face2 next
             (Cexp_num 0) rest))
       (candle_cv_tame_subdiv_face_aux graph face vertex
         (Cexp_pair (Cexp_num 0) pending) rest))`;;

let candle_cv_tame_subdiv_face_def = new_definition
 `candle_cv_tame_subdiv_face graph face options =
    candle_cv_tame_subdiv_face_aux graph face
      (Cexp_fst (Cexp_fst options)) (Cexp_num 0) (Cexp_snd options)`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_subdiv";;

let candle_cv_tame_vertices_from_def = new_definition
 `candle_cv_tame_vertices_from face vertex =
    (let split = candle_cv_tame_split_at vertex
       (candle_cv_tame_face_vertices face) in
     Cexp_pair vertex
       (candle_cv_tame_list_append (Cexp_snd split) (Cexp_fst split)))`;;

let candle_cv_tame_indices_to_vertices_def = define
 `(candle_cv_tame_indices_to_vertices rotated (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_indices_to_vertices rotated (Cexp_pair index rest) =
     Cexp_pair (candle_cv_tame_list_nth (Cexp_num 0) rotated index)
       (candle_cv_tame_indices_to_vertices rotated rest))`;;

let candle_cv_tame_hide_dups_rec_def = define
 `(candle_cv_tame_hide_dups_rec previous (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_hide_dups_rec previous (Cexp_pair vertex rest) =
     Cexp_pair
       (Cexp_if (Cexp_eq previous vertex)
         (Cexp_num 0) (candle_cv_tame_some vertex))
       (candle_cv_tame_hide_dups_rec vertex rest))`;;

let candle_cv_tame_hide_dups_def = new_definition
 `candle_cv_tame_hide_dups vertices =
    Cexp_if (Cexp_ispair vertices)
      (Cexp_pair (candle_cv_tame_some (Cexp_fst vertices))
        (candle_cv_tame_hide_dups_rec
          (Cexp_fst vertices) (Cexp_snd vertices)))
      (Cexp_num 0)`;;

let candle_cv_tame_index_to_vertex_list_def = new_definition
 `candle_cv_tame_index_to_vertex_list face vertex indices =
    candle_cv_tame_hide_dups
      (candle_cv_tame_indices_to_vertices
        (candle_cv_tame_vertices_from face vertex) indices)`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_index";;

let candle_cv_tame_neighbors_def = define
 `(candle_cv_tame_neighbors vertex (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_neighbors vertex (Cexp_pair face rest) =
     Cexp_pair (candle_cv_tame_next_vertex face vertex)
       (candle_cv_tame_neighbors vertex rest))`;;

let candle_cv_tame_directed_length_def = new_definition
 `candle_cv_tame_directed_length face left right =
    Cexp_if (Cexp_eq left right) (Cexp_num 0)
      (Cexp_add
        (candle_cv_tame_list_length
          (candle_cv_tame_between
            (candle_cv_tame_face_vertices face) left right))
        (Cexp_num 1))`;;

let candle_cv_tame_duplicate_edge_def = new_definition
 `candle_cv_tame_duplicate_edge graph face left right =
    candle_cv_tame_and
      (candle_cv_tame_le (Cexp_num 2)
        (candle_cv_tame_directed_length face left right))
      (candle_cv_tame_and
        (candle_cv_tame_le (Cexp_num 2)
          (candle_cv_tame_directed_length face right left))
        (candle_cv_tame_list_member right
          (candle_cv_tame_neighbors left
            (candle_cv_tame_graph_faces_at_vertex graph left))))`;;

let candle_cv_tame_contains_unacceptable_snd_def = define
 `(candle_cv_tame_contains_unacceptable_snd graph face previous
       (Cexp_num n) = candle_cv_tame_false) /\
  (candle_cv_tame_contains_unacceptable_snd graph face previous
       (Cexp_pair current rest) =
     Cexp_if (Cexp_ispair rest)
       (let next = Cexp_fst rest in
        Cexp_if
          (candle_cv_tame_and (Cexp_less previous current)
            (candle_cv_tame_and (Cexp_less current next)
              (candle_cv_tame_duplicate_edge graph face current next)))
          candle_cv_tame_true
          (candle_cv_tame_contains_unacceptable_snd
            graph face current rest))
       candle_cv_tame_false)`;;

let candle_cv_tame_contains_duplicate_edge_def = new_definition
 `candle_cv_tame_contains_duplicate_edge graph face indices =
    Cexp_if (Cexp_ispair indices)
      (let first = Cexp_fst indices in
       let rest = Cexp_snd indices in
       Cexp_if (Cexp_ispair rest)
         (let second = Cexp_fst rest in
          Cexp_if
            (candle_cv_tame_and (Cexp_less first second)
              (candle_cv_tame_duplicate_edge graph face first second))
            candle_cv_tame_true
            (candle_cv_tame_contains_unacceptable_snd
              graph face first rest))
         candle_cv_tame_false)
      candle_cv_tame_false`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_duplicate";;

let candle_cv_tame_generate_polygon_from_enum_def = define
 `(candle_cv_tame_generate_polygon_from_enum graph face vertex
       (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_generate_polygon_from_enum graph face vertex
       (Cexp_pair indices rest) =
     Cexp_if (candle_cv_tame_contains_duplicate_edge graph face indices)
       (candle_cv_tame_generate_polygon_from_enum graph face vertex rest)
       (Cexp_pair
         (candle_cv_tame_subdiv_face graph face
           (candle_cv_tame_index_to_vertex_list face vertex indices))
         (candle_cv_tame_generate_polygon_from_enum
           graph face vertex rest)))`;;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD definitions_complete";;

(* All-variable equations admitted by the verified evaluator. *)

let candle_cv_tame_replace_faces_at_compute = prove
 (`!indices old replacement tables.
    candle_cv_tame_replace_faces_at indices old replacement tables =
      Cexp_if (Cexp_ispair indices)
        (let index = Cexp_fst indices in
         let current = candle_cv_tame_list_nth (Cexp_num 0) tables index in
         let updated = candle_cv_tame_list_replace old replacement current in
         candle_cv_tame_replace_faces_at (Cexp_snd indices) old replacement
           (candle_cv_tame_list_update tables index updated))
        tables`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `indices:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_replace_faces_at_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_replace";;

let candle_cv_tame_map_face_lists_replace_compute = prove
 (`!old replacement tables.
    candle_cv_tame_map_face_lists_replace old replacement tables =
      Cexp_if (Cexp_ispair tables)
        (Cexp_pair
          (candle_cv_tame_list_replace old replacement (Cexp_fst tables))
          (candle_cv_tame_map_face_lists_replace old replacement
            (Cexp_snd tables)))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `tables:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_map_face_lists_replace_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let candle_cv_tame_fresh_vertices_compute = prove
 (`!current controls. candle_cv_tame_fresh_vertices current controls =
    Cexp_if (Cexp_ispair controls)
      (Cexp_pair current
        (candle_cv_tame_fresh_vertices
          (Cexp_add current (Cexp_num 1)) (Cexp_snd controls)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `controls:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_fresh_vertices_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_snd_def));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_fresh";;

let candle_cv_tame_heights_new_aux_compute = prove
 (`!h1 h2 total index controls.
    candle_cv_tame_heights_new_aux h1 h2 total index controls =
      Cexp_if (Cexp_ispair controls)
        (Cexp_pair
          (candle_cv_tame_min_num
            (Cexp_add h1 (Cexp_add index (Cexp_num 1)))
            (Cexp_add h2 (Cexp_sub total index)))
          (candle_cv_tame_heights_new_aux h1 h2 total
            (Cexp_add index (Cexp_num 1)) (Cexp_snd controls)))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `controls:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_heights_new_aux_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_snd_def));;

let candle_cv_tame_replicate_face_pair_compute = prove
 (`!face_pair controls.
    candle_cv_tame_replicate_face_pair face_pair controls =
      Cexp_if (Cexp_ispair controls)
        (Cexp_pair face_pair
          (candle_cv_tame_replicate_face_pair face_pair (Cexp_snd controls)))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `controls:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_replicate_face_pair_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_snd_def));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_heights";;

let candle_cv_tame_subdiv_face_aux_compute = prove
 (`!graph face vertex pending options.
    candle_cv_tame_subdiv_face_aux graph face vertex pending options =
      Cexp_if (Cexp_ispair options)
        (let option_value = Cexp_fst options in
         let rest = Cexp_snd options in
         Cexp_if (Cexp_ispair option_value)
           (let next = Cexp_fst option_value in
            Cexp_if
              (candle_cv_tame_and
                (Cexp_eq (candle_cv_tame_next_vertex face vertex) next)
                (candle_cv_tame_not (Cexp_ispair pending)))
              (candle_cv_tame_subdiv_face_aux graph face next
                (Cexp_num 0) rest)
              (let new_vertices = candle_cv_tame_fresh_vertices
                 (candle_cv_tame_graph_vertex_count graph) pending in
               let split = candle_cv_tame_split_face_graph_exact
                 graph vertex next face new_vertices in
               let face2 = Cexp_fst (Cexp_snd split) in
               let next_graph = Cexp_snd (Cexp_snd split) in
               candle_cv_tame_subdiv_face_aux next_graph face2 next
                 (Cexp_num 0) rest))
           (candle_cv_tame_subdiv_face_aux graph face vertex
             (Cexp_pair (Cexp_num 0) pending) rest))
        (candle_cv_tame_make_face_final face graph)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `options:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_subdiv_face_aux_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_subdiv";;

let candle_cv_tame_indices_to_vertices_compute = prove
 (`!rotated indices. candle_cv_tame_indices_to_vertices rotated indices =
    Cexp_if (Cexp_ispair indices)
      (Cexp_pair
        (candle_cv_tame_list_nth (Cexp_num 0) rotated (Cexp_fst indices))
        (candle_cv_tame_indices_to_vertices rotated (Cexp_snd indices)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `indices:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_indices_to_vertices_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let candle_cv_tame_hide_dups_rec_compute = prove
 (`!previous vertices. candle_cv_tame_hide_dups_rec previous vertices =
    Cexp_if (Cexp_ispair vertices)
      (Cexp_pair
        (Cexp_if (Cexp_eq previous (Cexp_fst vertices))
          (Cexp_num 0) (candle_cv_tame_some (Cexp_fst vertices)))
        (candle_cv_tame_hide_dups_rec
          (Cexp_fst vertices) (Cexp_snd vertices)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `vertices:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_hide_dups_rec_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_indices";;

let candle_cv_tame_neighbors_compute = prove
 (`!vertex faces. candle_cv_tame_neighbors vertex faces =
    Cexp_if (Cexp_ispair faces)
      (Cexp_pair (candle_cv_tame_next_vertex (Cexp_fst faces) vertex)
        (candle_cv_tame_neighbors vertex (Cexp_snd faces)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_neighbors_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let candle_cv_tame_contains_unacceptable_snd_compute = prove
 (`!graph face previous indices.
    candle_cv_tame_contains_unacceptable_snd graph face previous indices =
      Cexp_if (Cexp_ispair indices)
        (let current = Cexp_fst indices in
         let rest = Cexp_snd indices in
         Cexp_if (Cexp_ispair rest)
           (let next = Cexp_fst rest in
            Cexp_if
              (candle_cv_tame_and (Cexp_less previous current)
                (candle_cv_tame_and (Cexp_less current next)
                  (candle_cv_tame_duplicate_edge graph face current next)))
              candle_cv_tame_true
              (candle_cv_tame_contains_unacceptable_snd
                graph face current rest))
           candle_cv_tame_false)
        candle_cv_tame_false`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `indices:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_contains_unacceptable_snd_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proof_duplicate";;

let candle_cv_tame_generate_polygon_from_enum_compute = prove
 (`!graph face vertex enumeration.
    candle_cv_tame_generate_polygon_from_enum graph face vertex enumeration =
      Cexp_if (Cexp_ispair enumeration)
        (Cexp_if
          (candle_cv_tame_contains_duplicate_edge graph face
            (Cexp_fst enumeration))
          (candle_cv_tame_generate_polygon_from_enum graph face vertex
            (Cexp_snd enumeration))
          (Cexp_pair
            (candle_cv_tame_subdiv_face graph face
              (candle_cv_tame_index_to_vertex_list face vertex
                (Cexp_fst enumeration)))
            (candle_cv_tame_generate_polygon_from_enum graph face vertex
              (Cexp_snd enumeration))))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `enumeration:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_generate_polygon_from_enum_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let _ = print_endline "CANDLE_CV_TAME_SUCCESSOR_LOAD proofs_complete";;

let candle_cv_tame_successor_compute_eqs =
  candle_cv_tame_enumerator_core_compute_eqs @
  map SPEC_ALL
   [candle_cv_tame_singleton_def;
    candle_cv_tame_some_def;
    candle_cv_tame_min_num_def;
    candle_cv_tame_replace_faces_at_compute;
    candle_cv_tame_map_face_lists_replace_compute;
    candle_cv_tame_make_face_final_def;
    candle_cv_tame_fresh_vertices_compute;
    candle_cv_tame_heights_new_aux_compute;
    candle_cv_tame_heights_new_vertices_def;
    candle_cv_tame_split_face_def;
    candle_cv_tame_replicate_face_pair_compute;
    candle_cv_tame_split_face_graph_exact_def;
    candle_cv_tame_subdiv_face_aux_compute;
    candle_cv_tame_subdiv_face_def;
    candle_cv_tame_vertices_from_def;
    candle_cv_tame_indices_to_vertices_compute;
    candle_cv_tame_hide_dups_rec_compute;
    candle_cv_tame_hide_dups_def;
    candle_cv_tame_index_to_vertex_list_def;
    candle_cv_tame_neighbors_compute;
    candle_cv_tame_directed_length_def;
    candle_cv_tame_duplicate_edge_def;
    candle_cv_tame_contains_unacceptable_snd_compute;
    candle_cv_tame_contains_duplicate_edge_def;
    candle_cv_tame_generate_polygon_from_enum_compute];;

let candle_cv_tame_successor_compute tm =
  compute candle_cv_tame_successor_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_SUCCESSOR_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
