(* ========================================================================== *)
(* Faithful executable foundations for the AFP tame-graph enumerator.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This module fixes the cval representation used *)
(* by the intended Kernel.compute route and implements the exact finite-list  *)
(* and graph selectors needed by successor generation.  It is not yet the     *)
(* complete next_tame replay and carries no classification authority.          *)
(* ========================================================================== *)

needs "candle/compute.ml";;

module Candle_cv_tame_graph_enumerator_core = struct

(* Representation (all components are cvals):                                *)
(*   list       = 0 | pair head tail                                           *)
(*   bool       = 0 | 1                                                        *)
(*   option     = 0 | pair value 0                                             *)
(*   face       = pair vertices final_flag                                     *)
(*   graph      = pair faces (pair vertex_count (pair faces_at heights))        *)

let candle_cv_tame_false_def = new_definition
 `candle_cv_tame_false = Cexp_num 0`;;

let candle_cv_tame_true_def = new_definition
 `candle_cv_tame_true = Cexp_num 1`;;

let candle_cv_tame_not_def = new_definition
 `candle_cv_tame_not value =
    Cexp_if value candle_cv_tame_false candle_cv_tame_true`;;

let candle_cv_tame_and_def = new_definition
 `candle_cv_tame_and left right =
    Cexp_if left right candle_cv_tame_false`;;

let candle_cv_tame_or_def = new_definition
 `candle_cv_tame_or left right =
    Cexp_if left candle_cv_tame_true right`;;

let candle_cv_tame_le_def = new_definition
 `candle_cv_tame_le left right =
    candle_cv_tame_not (Cexp_less right left)`;;

let candle_cv_tame_list_append_def = define
 `(candle_cv_tame_list_append (Cexp_num n) right = right) /\
  (candle_cv_tame_list_append (Cexp_pair head tail) right =
     Cexp_pair head (candle_cv_tame_list_append tail right))`;;

let candle_cv_tame_list_reverse_aux_def = define
 `(candle_cv_tame_list_reverse_aux acc (Cexp_num n) = acc) /\
  (candle_cv_tame_list_reverse_aux acc (Cexp_pair head tail) =
     candle_cv_tame_list_reverse_aux (Cexp_pair head acc) tail)`;;

let candle_cv_tame_list_reverse_def = new_definition
 `candle_cv_tame_list_reverse values =
    candle_cv_tame_list_reverse_aux (Cexp_num 0) values`;;

let candle_cv_tame_list_length_def = define
 `(candle_cv_tame_list_length (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_list_length (Cexp_pair head tail) =
     Cexp_add (Cexp_num 1) (candle_cv_tame_list_length tail))`;;

let candle_cv_tame_list_member_def = define
 `(candle_cv_tame_list_member value (Cexp_num n) = candle_cv_tame_false) /\
  (candle_cv_tame_list_member value (Cexp_pair head tail) =
     Cexp_if (Cexp_eq value head)
       candle_cv_tame_true
       (candle_cv_tame_list_member value tail))`;;

let candle_cv_tame_list_last_def = define
 `(candle_cv_tame_list_last default (Cexp_num n) = default) /\
  (candle_cv_tame_list_last default (Cexp_pair head tail) =
     Cexp_if (Cexp_ispair tail)
       (candle_cv_tame_list_last head tail)
       head)`;;

let candle_cv_tame_list_nth_def = define
 `(candle_cv_tame_list_nth default (Cexp_num n) index = default) /\
  (candle_cv_tame_list_nth default (Cexp_pair head tail) index =
     Cexp_if (Cexp_eq index (Cexp_num 0))
       head
       (candle_cv_tame_list_nth default tail
         (Cexp_sub index (Cexp_num 1))))`;;

let candle_cv_tame_list_update_def = define
 `(candle_cv_tame_list_update (Cexp_num n) index value = Cexp_num n) /\
  (candle_cv_tame_list_update (Cexp_pair head tail) index value =
     Cexp_if (Cexp_eq index (Cexp_num 0))
       (Cexp_pair value tail)
       (Cexp_pair head
         (candle_cv_tame_list_update tail
           (Cexp_sub index (Cexp_num 1)) value)))`;;

let candle_cv_tame_list_replace_def = define
 `(candle_cv_tame_list_replace old replacement (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_list_replace old replacement (Cexp_pair head tail) =
     Cexp_if (Cexp_eq head old)
       (candle_cv_tame_list_append replacement tail)
       (Cexp_pair head
         (candle_cv_tame_list_replace old replacement tail)))`;;

let candle_cv_tame_list_replicate_num_def =
  new_recursive_definition num_RECURSION
   `(candle_cv_tame_list_replicate_num value 0 = Cexp_num 0) /\
    (candle_cv_tame_list_replicate_num value (SUC n) =
       Cexp_pair value (candle_cv_tame_list_replicate_num value n))`;;

let candle_cv_tame_list_replicate_def = define
 `(candle_cv_tame_list_replicate value (Cexp_num n) =
     candle_cv_tame_list_replicate_num value n) /\
  (candle_cv_tame_list_replicate value (Cexp_pair x y) = Cexp_num 0)`;;

let candle_cv_tame_list_upt_num_def =
  new_recursive_definition num_RECURSION
   `(candle_cv_tame_list_upt_num start 0 = Cexp_num 0) /\
    (candle_cv_tame_list_upt_num start (SUC n) =
       Cexp_pair (Cexp_num start)
         (candle_cv_tame_list_upt_num (SUC start) n))`;;

let candle_cv_tame_list_upt_count_def = define
 `(candle_cv_tame_list_upt_count (Cexp_num start) (Cexp_num count) =
     candle_cv_tame_list_upt_num start count) /\
  (candle_cv_tame_list_upt_count (Cexp_pair a b) ccount = Cexp_num 0) /\
  (candle_cv_tame_list_upt_count cstart (Cexp_pair x y) = Cexp_num 0)`;;

let candle_cv_tame_list_upt_def = new_definition
 `candle_cv_tame_list_upt start finish =
    candle_cv_tame_list_upt_count start (Cexp_sub finish start)`;;

let candle_cv_tame_split_at_rec_def = define
 `(candle_cv_tame_split_at_rec needle before (Cexp_num n) =
     Cexp_pair before (Cexp_num 0)) /\
  (candle_cv_tame_split_at_rec needle before (Cexp_pair head tail) =
     Cexp_if (Cexp_eq head needle)
       (Cexp_pair before tail)
       (candle_cv_tame_split_at_rec needle
         (candle_cv_tame_list_append before (Cexp_pair head (Cexp_num 0)))
         tail))`;;

let candle_cv_tame_split_at_def = new_definition
 `candle_cv_tame_split_at needle values =
    candle_cv_tame_split_at_rec needle (Cexp_num 0) values`;;

let candle_cv_tame_between_def = new_definition
 `candle_cv_tame_between values ram1 ram2 =
    (let split1 = candle_cv_tame_split_at ram1 values in
     let pre1 = Cexp_fst split1 in
     let post1 = Cexp_snd split1 in
     Cexp_if (candle_cv_tame_list_member ram2 post1)
       (Cexp_fst (candle_cv_tame_split_at ram2 post1))
       (candle_cv_tame_list_append post1
         (Cexp_fst (candle_cv_tame_split_at ram2 pre1))))`;;

let candle_cv_tame_face_def = new_definition
 `candle_cv_tame_face vertices final_flag =
    Cexp_pair vertices final_flag`;;

let candle_cv_tame_face_vertices_def = new_definition
 `candle_cv_tame_face_vertices face = Cexp_fst face`;;

let candle_cv_tame_face_final_def = new_definition
 `candle_cv_tame_face_final face = Cexp_snd face`;;

let candle_cv_tame_face_set_final_def = new_definition
 `candle_cv_tame_face_set_final face =
    candle_cv_tame_face (candle_cv_tame_face_vertices face)
      candle_cv_tame_true`;;

let candle_cv_tame_graph_def = new_definition
 `candle_cv_tame_graph faces vertex_count faces_at heights =
    Cexp_pair faces
      (Cexp_pair vertex_count (Cexp_pair faces_at heights))`;;

let candle_cv_tame_graph_faces_def = new_definition
 `candle_cv_tame_graph_faces graph = Cexp_fst graph`;;

let candle_cv_tame_graph_vertex_count_def = new_definition
 `candle_cv_tame_graph_vertex_count graph = Cexp_fst (Cexp_snd graph)`;;

let candle_cv_tame_graph_faces_at_def = new_definition
 `candle_cv_tame_graph_faces_at graph = Cexp_fst (Cexp_snd (Cexp_snd graph))`;;

let candle_cv_tame_graph_heights_def = new_definition
 `candle_cv_tame_graph_heights graph = Cexp_snd (Cexp_snd (Cexp_snd graph))`;;

let candle_cv_tame_graph_faces_at_vertex_def = new_definition
 `candle_cv_tame_graph_faces_at_vertex graph vertex =
    candle_cv_tame_list_nth (Cexp_num 0)
      (candle_cv_tame_graph_faces_at graph) vertex`;;

let candle_cv_tame_graph_height_def = new_definition
 `candle_cv_tame_graph_height graph vertex =
    candle_cv_tame_list_nth (Cexp_num 0)
      (candle_cv_tame_graph_heights graph) vertex`;;

let candle_cv_tame_filter_final_def = define
 `(candle_cv_tame_filter_final wanted (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_filter_final wanted (Cexp_pair face rest) =
     Cexp_if (Cexp_eq (candle_cv_tame_face_final face) wanted)
       (Cexp_pair face (candle_cv_tame_filter_final wanted rest))
       (candle_cv_tame_filter_final wanted rest))`;;

let candle_cv_tame_graph_finals_def = new_definition
 `candle_cv_tame_graph_finals graph =
    candle_cv_tame_filter_final candle_cv_tame_true
      (candle_cv_tame_graph_faces graph)`;;

let candle_cv_tame_graph_nonfinals_def = new_definition
 `candle_cv_tame_graph_nonfinals graph =
    candle_cv_tame_filter_final candle_cv_tame_false
      (candle_cv_tame_graph_faces graph)`;;

let candle_cv_tame_graph_final_def = new_definition
 `candle_cv_tame_graph_final graph =
    candle_cv_tame_not
      (Cexp_ispair (candle_cv_tame_graph_nonfinals graph))`;;

let candle_cv_tame_next_elem_def = define
 `(candle_cv_tame_next_elem (Cexp_num n) fallback value = fallback) /\
  (candle_cv_tame_next_elem (Cexp_pair head tail) fallback value =
     Cexp_if (Cexp_eq value head)
       (Cexp_if (Cexp_ispair tail) (Cexp_fst tail) fallback)
       (candle_cv_tame_next_elem tail fallback value))`;;

let candle_cv_tame_next_vertex_def = new_definition
 `candle_cv_tame_next_vertex face vertex =
    (let vertices = candle_cv_tame_face_vertices face in
     candle_cv_tame_next_elem vertices (Cexp_fst vertices) vertex)`;;

let candle_cv_tame_next_vertices_num_def =
  new_recursive_definition num_RECURSION
   `(candle_cv_tame_next_vertices_num face vertex 0 = vertex) /\
    (candle_cv_tame_next_vertices_num face vertex (SUC n) =
       candle_cv_tame_next_vertices_num face
         (candle_cv_tame_next_vertex face vertex) n)`;;

let candle_cv_tame_next_vertices_def = define
 `(candle_cv_tame_next_vertices face vertex (Cexp_num n) =
     candle_cv_tame_next_vertices_num face vertex n) /\
  (candle_cv_tame_next_vertices face vertex (Cexp_pair x y) = vertex)`;;

let candle_cv_tame_min_face_def = define
 `(candle_cv_tame_min_face (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_min_face (Cexp_pair face rest) =
     Cexp_if (Cexp_ispair rest)
       (let rest_min = candle_cv_tame_min_face rest in
        Cexp_if
          (candle_cv_tame_le
            (candle_cv_tame_list_length
              (candle_cv_tame_face_vertices face))
            (candle_cv_tame_list_length
              (candle_cv_tame_face_vertices rest_min)))
          face rest_min)
       face)`;;

let candle_cv_tame_min_vertex_def = define
 `(candle_cv_tame_min_vertex graph (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_min_vertex graph (Cexp_pair vertex rest) =
     Cexp_if (Cexp_ispair rest)
       (let rest_min = candle_cv_tame_min_vertex graph rest in
        Cexp_if
          (candle_cv_tame_le
            (candle_cv_tame_graph_height graph vertex)
            (candle_cv_tame_graph_height graph rest_min))
          vertex rest_min)
       vertex)`;;

let candle_cv_tame_seed_def = new_definition
 `candle_cv_tame_seed parameter =
    (let vertex_count = Cexp_add parameter (Cexp_num 3) in
     let vertices = candle_cv_tame_list_upt (Cexp_num 0) vertex_count in
     let final_face = candle_cv_tame_face vertices candle_cv_tame_true in
     let open_face = candle_cv_tame_face
       (candle_cv_tame_list_reverse vertices) candle_cv_tame_false in
     let faces = Cexp_pair final_face (Cexp_pair open_face (Cexp_num 0)) in
     candle_cv_tame_graph faces vertex_count
       (candle_cv_tame_list_replicate faces vertex_count)
       (candle_cv_tame_list_replicate (Cexp_num 0) vertex_count))`;;

(* All-variable characteristic equations for Kernel.compute. *)

let candle_cv_tame_list_append_compute = prove
 (`!left right. candle_cv_tame_list_append left right =
     Cexp_if (Cexp_ispair left)
       (Cexp_pair (Cexp_fst left)
         (candle_cv_tame_list_append (Cexp_snd left) right))
       right`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `left:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_append_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_reverse_aux_compute = prove
 (`!acc values. candle_cv_tame_list_reverse_aux acc values =
     Cexp_if (Cexp_ispair values)
       (candle_cv_tame_list_reverse_aux
         (Cexp_pair (Cexp_fst values) acc) (Cexp_snd values))
       acc`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_reverse_aux_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_length_compute = prove
 (`!values. candle_cv_tame_list_length values =
     Cexp_if (Cexp_ispair values)
       (Cexp_add (Cexp_num 1)
         (candle_cv_tame_list_length (Cexp_snd values)))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_length_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_tame_list_member_compute = prove
 (`!value values. candle_cv_tame_list_member value values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq value (Cexp_fst values))
         candle_cv_tame_true
         (candle_cv_tame_list_member value (Cexp_snd values)))
       candle_cv_tame_false`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_member_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_last_compute = prove
 (`!default values. candle_cv_tame_list_last default values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_ispair (Cexp_snd values))
         (candle_cv_tame_list_last (Cexp_fst values) (Cexp_snd values))
         (Cexp_fst values))
       default`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_last_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_nth_compute = prove
 (`!default values index. candle_cv_tame_list_nth default values index =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq index (Cexp_num 0))
         (Cexp_fst values)
         (candle_cv_tame_list_nth default (Cexp_snd values)
           (Cexp_sub index (Cexp_num 1))))
       default`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_nth_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_update_compute = prove
 (`!values index value. candle_cv_tame_list_update values index value =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq index (Cexp_num 0))
         (Cexp_pair value (Cexp_snd values))
         (Cexp_pair (Cexp_fst values)
           (candle_cv_tame_list_update (Cexp_snd values)
             (Cexp_sub index (Cexp_num 1)) value)))
       values`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_update_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_list_replace_compute = prove
 (`!old replacement values. candle_cv_tame_list_replace old replacement values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq (Cexp_fst values) old)
         (candle_cv_tame_list_append replacement (Cexp_snd values))
         (Cexp_pair (Cexp_fst values)
           (candle_cv_tame_list_replace old replacement (Cexp_snd values))))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_list_replace_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_split_at_rec_compute = prove
 (`!needle before values. candle_cv_tame_split_at_rec needle before values =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq (Cexp_fst values) needle)
         (Cexp_pair before (Cexp_snd values))
         (candle_cv_tame_split_at_rec needle
           (candle_cv_tame_list_append before
             (Cexp_pair (Cexp_fst values) (Cexp_num 0)))
           (Cexp_snd values)))
       (Cexp_pair before (Cexp_num 0))`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_split_at_rec_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_filter_final_compute = prove
 (`!wanted faces. candle_cv_tame_filter_final wanted faces =
     Cexp_if (Cexp_ispair faces)
       (Cexp_if
         (Cexp_eq (candle_cv_tame_face_final (Cexp_fst faces)) wanted)
         (Cexp_pair (Cexp_fst faces)
           (candle_cv_tame_filter_final wanted (Cexp_snd faces)))
         (candle_cv_tame_filter_final wanted (Cexp_snd faces)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_filter_final_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_next_elem_compute = prove
 (`!values fallback value. candle_cv_tame_next_elem values fallback value =
     Cexp_if (Cexp_ispair values)
       (Cexp_if (Cexp_eq value (Cexp_fst values))
         (Cexp_if (Cexp_ispair (Cexp_snd values))
           (Cexp_fst (Cexp_snd values)) fallback)
         (candle_cv_tame_next_elem (Cexp_snd values) fallback value))
       fallback`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_next_elem_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_min_face_compute = prove
 (`!faces. candle_cv_tame_min_face faces =
     Cexp_if (Cexp_ispair faces)
       (Cexp_if (Cexp_ispair (Cexp_snd faces))
         (let rest_min = candle_cv_tame_min_face (Cexp_snd faces) in
          Cexp_if
            (candle_cv_tame_le
              (candle_cv_tame_list_length
                (candle_cv_tame_face_vertices (Cexp_fst faces)))
              (candle_cv_tame_list_length
                (candle_cv_tame_face_vertices rest_min)))
            (Cexp_fst faces) rest_min)
         (Cexp_fst faces))
       (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_min_face_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_min_vertex_compute = prove
 (`!graph vertices. candle_cv_tame_min_vertex graph vertices =
     Cexp_if (Cexp_ispair vertices)
       (Cexp_if (Cexp_ispair (Cexp_snd vertices))
         (let rest_min = candle_cv_tame_min_vertex graph (Cexp_snd vertices) in
          Cexp_if
            (candle_cv_tame_le
              (candle_cv_tame_graph_height graph (Cexp_fst vertices))
              (candle_cv_tame_graph_height graph rest_min))
            (Cexp_fst vertices) rest_min)
         (Cexp_fst vertices))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `vertices:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_min_vertex_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_enumerator_core_compute_eqs =
  map SPEC_ALL
   [candle_cv_tame_false_def;
    candle_cv_tame_true_def;
    candle_cv_tame_not_def;
    candle_cv_tame_and_def;
    candle_cv_tame_or_def;
    candle_cv_tame_le_def;
    candle_cv_tame_list_append_compute;
    candle_cv_tame_list_reverse_aux_compute;
    candle_cv_tame_list_reverse_def;
    candle_cv_tame_list_length_compute;
    candle_cv_tame_list_member_compute;
    candle_cv_tame_list_last_compute;
    candle_cv_tame_list_nth_compute;
    candle_cv_tame_list_update_compute;
    candle_cv_tame_list_replace_compute;
    candle_cv_tame_split_at_rec_compute;
    candle_cv_tame_split_at_def;
    candle_cv_tame_between_def;
    candle_cv_tame_face_def;
    candle_cv_tame_face_vertices_def;
    candle_cv_tame_face_final_def;
    candle_cv_tame_face_set_final_def;
    candle_cv_tame_graph_def;
    candle_cv_tame_graph_faces_def;
    candle_cv_tame_graph_vertex_count_def;
    candle_cv_tame_graph_faces_at_def;
    candle_cv_tame_graph_heights_def;
    candle_cv_tame_graph_faces_at_vertex_def;
    candle_cv_tame_graph_height_def;
    candle_cv_tame_filter_final_compute;
    candle_cv_tame_graph_finals_def;
    candle_cv_tame_graph_nonfinals_def;
    candle_cv_tame_graph_final_def;
    candle_cv_tame_next_elem_compute;
    candle_cv_tame_next_vertex_def;
    candle_cv_tame_min_face_compute;
    candle_cv_tame_min_vertex_compute];;

(* These constructor equations specify source/fixture preparation.  Candle's *)
(* verified compute primitive deliberately fixes its initialization theorem  *)
(* set and rejects constructor patterns in the program-equation list.  They   *)
(* therefore remain ordinary HOL rewrite theorems and are not supplied to     *)
(* Kernel.compute.  Enumeration loop controls will use checked list data so   *)
(* that the eventual evaluator program remains entirely all-variable.         *)

let candle_cv_tame_enumerator_core_init_eqs =
  CONJUNCTS candle_cv_tame_list_replicate_num_def @
  CONJUNCTS candle_cv_tame_list_replicate_def @
  CONJUNCTS candle_cv_tame_list_upt_num_def @
  CONJUNCTS candle_cv_tame_list_upt_count_def @
  [SPEC_ALL candle_cv_tame_list_upt_def] @
  CONJUNCTS candle_cv_tame_next_vertices_num_def @
  CONJUNCTS candle_cv_tame_next_vertices_def;;

let candle_cv_tame_enumerator_compute tm =
  compute candle_cv_tame_enumerator_core_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_ENUMERATOR_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
