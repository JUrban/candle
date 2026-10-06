(* ========================================================================== *)
(* Faithful reflected scoring for the AFP tame-graph enumerator.              *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is the executable content of the          *)
(* Generator.faceSquanderLowerBound, ExcessAt, ExcessTable, deleteAround,      *)
(* ExcessNotAtRec, squanderLowerBound, and polysizes definitions.  Candidate   *)
(* polygon sizes are supplied as the exact finite interval [3..maxGon p]; the  *)
(* score-dependent filtering itself is performed by Kernel.compute.           *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_pruning.ml";;

module Candle_cv_tame_graph_scoring = struct

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;
open Candle_cv_tame_graph_pruning;;

let candle_cv_tame_squander_target_def = new_definition
 `candle_cv_tame_squander_target = Cexp_num 15410`;;

let candle_cv_tame_excess_t_count_def = new_definition
 `candle_cv_tame_excess_t_count = Cexp_num 6295`;;

let candle_cv_tame_max_num_def = new_definition
 `candle_cv_tame_max_num left right =
    Cexp_if (candle_cv_tame_le left right) right left`;;

(* Exact AFP Tame.squanderFace table. *)
let candle_cv_tame_squander_face_def = new_definition
 `candle_cv_tame_squander_face size =
    Cexp_if (Cexp_eq size (Cexp_num 3)) (Cexp_num 0)
      (Cexp_if (Cexp_eq size (Cexp_num 4)) (Cexp_num 2058)
        (Cexp_if (Cexp_eq size (Cexp_num 5)) (Cexp_num 4819)
          (Cexp_if (Cexp_eq size (Cexp_num 6)) (Cexp_num 7120)
            candle_cv_tame_squander_target)))`;;

(* Exact AFP Tame.squanderVertex table. *)
let candle_cv_tame_squander_vertex_def = new_definition
 `candle_cv_tame_squander_vertex triangles quadrilaterals =
    Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 0))
        (Cexp_eq quadrilaterals (Cexp_num 3))) (Cexp_num 6177)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 0))
        (Cexp_eq quadrilaterals (Cexp_num 4))) (Cexp_num 9696)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 1))
        (Cexp_eq quadrilaterals (Cexp_num 2))) (Cexp_num 6557)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 1))
        (Cexp_eq quadrilaterals (Cexp_num 3))) (Cexp_num 6176)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 2))
        (Cexp_eq quadrilaterals (Cexp_num 1))) (Cexp_num 7967)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 2))
        (Cexp_eq quadrilaterals (Cexp_num 2))) (Cexp_num 4116)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 2))
        (Cexp_eq quadrilaterals (Cexp_num 3))) (Cexp_num 12846)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 3))
        (Cexp_eq quadrilaterals (Cexp_num 1))) (Cexp_num 3106)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 3))
        (Cexp_eq quadrilaterals (Cexp_num 2))) (Cexp_num 8165)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 4))
        (Cexp_eq quadrilaterals (Cexp_num 0))) (Cexp_num 3466)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 4))
        (Cexp_eq quadrilaterals (Cexp_num 1))) (Cexp_num 3655)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 5))
        (Cexp_eq quadrilaterals (Cexp_num 0))) (Cexp_num 395)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 5))
        (Cexp_eq quadrilaterals (Cexp_num 1))) (Cexp_num 11354)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 6))
        (Cexp_eq quadrilaterals (Cexp_num 0))) (Cexp_num 6854)
    (Cexp_if
      (candle_cv_tame_and
        (Cexp_eq triangles (Cexp_num 7))
        (Cexp_eq quadrilaterals (Cexp_num 0))) (Cexp_num 14493)
      candle_cv_tame_squander_target))))))))))))))`;;

let candle_cv_tame_face_squander_sum_def = define
 `(candle_cv_tame_face_squander_sum (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_face_squander_sum (Cexp_pair face rest) =
     Cexp_add
       (Cexp_if (candle_cv_tame_face_final face)
         (candle_cv_tame_squander_face
           (candle_cv_tame_list_length
             (candle_cv_tame_face_vertices face)))
         (Cexp_num 0))
       (candle_cv_tame_face_squander_sum rest))`;;

let candle_cv_tame_all_faces_final_def = define
 `(candle_cv_tame_all_faces_final (Cexp_num n) = candle_cv_tame_true) /\
  (candle_cv_tame_all_faces_final (Cexp_pair face rest) =
     candle_cv_tame_and (candle_cv_tame_face_final face)
       (candle_cv_tame_all_faces_final rest))`;;

let candle_cv_tame_count_final_size_def = define
 `(candle_cv_tame_count_final_size wanted (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_count_final_size wanted (Cexp_pair face rest) =
     Cexp_add
       (Cexp_if
         (candle_cv_tame_and
           (candle_cv_tame_face_final face)
           (Cexp_eq
             (candle_cv_tame_list_length
               (candle_cv_tame_face_vertices face)) wanted))
         (Cexp_num 1) (Cexp_num 0))
       (candle_cv_tame_count_final_size wanted rest))`;;

let candle_cv_tame_count_final_exceptional_def = define
 `(candle_cv_tame_count_final_exceptional (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_count_final_exceptional (Cexp_pair face rest) =
     Cexp_add
       (Cexp_if (candle_cv_tame_face_exceptional face)
         (Cexp_num 1) (Cexp_num 0))
       (candle_cv_tame_count_final_exceptional rest))`;;

(* Exact AFP Generator.excessAtType, including natural-number subtraction. *)
let candle_cv_tame_excess_at_type_def = new_definition
 `candle_cv_tame_excess_at_type triangles quadrilaterals exceptional =
    Cexp_if (Cexp_eq exceptional (Cexp_num 0))
      (Cexp_if
        (Cexp_less (Cexp_num 7) (Cexp_add triangles quadrilaterals))
        candle_cv_tame_squander_target
        (Cexp_sub
          (Cexp_sub
            (candle_cv_tame_squander_vertex triangles quadrilaterals)
            (Cexp_mul triangles
              (candle_cv_tame_squander_face (Cexp_num 3))))
          (Cexp_mul quadrilaterals
            (candle_cv_tame_squander_face (Cexp_num 4)))))
      (Cexp_if
        (candle_cv_tame_not
          (Cexp_eq (Cexp_add (Cexp_add triangles quadrilaterals) exceptional)
            (Cexp_num 6)))
        (Cexp_num 0)
        (Cexp_if (Cexp_eq triangles (Cexp_num 5))
          candle_cv_tame_excess_t_count
          candle_cv_tame_squander_target))`;;

let candle_cv_tame_excess_at_faces_def = new_definition
 `candle_cv_tame_excess_at_faces faces =
    Cexp_if (candle_cv_tame_all_faces_final faces)
      (candle_cv_tame_excess_at_type
        (candle_cv_tame_count_final_size (Cexp_num 3) faces)
        (candle_cv_tame_count_final_size (Cexp_num 4) faces)
        (candle_cv_tame_count_final_exceptional faces))
      (Cexp_num 0)`;;

let candle_cv_tame_excess_at_def = new_definition
 `candle_cv_tame_excess_at graph vertex =
    candle_cv_tame_excess_at_faces
      (candle_cv_tame_graph_faces_at_vertex graph vertex)`;;

(* face_lists are in vertex order, exactly as Graph.faceListAt. *)
let candle_cv_tame_excess_table_aux_def = define
 `(candle_cv_tame_excess_table_aux index (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_excess_table_aux index (Cexp_pair faces rest) =
     (let excess = candle_cv_tame_excess_at_faces faces in
      Cexp_if (Cexp_less (Cexp_num 0) excess)
        (Cexp_pair (Cexp_pair index excess)
          (candle_cv_tame_excess_table_aux
            (Cexp_add index (Cexp_num 1)) rest))
        (candle_cv_tame_excess_table_aux
          (Cexp_add index (Cexp_num 1)) rest)))`;;

let candle_cv_tame_excess_table_def = new_definition
 `candle_cv_tame_excess_table graph =
    candle_cv_tame_excess_table_aux (Cexp_num 0)
      (candle_cv_tame_graph_faces_at graph)`;;

(* Exact executable form of concat(map vs (facesAt g v)) in deleteAround. *)
let candle_cv_tame_around_keys_def = define
 `(candle_cv_tame_around_keys vertex (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_around_keys vertex (Cexp_pair face rest) =
     (let neighbor = candle_cv_tame_next_vertex face vertex in
      Cexp_pair neighbor
        (Cexp_if
          (Cexp_eq
            (candle_cv_tame_list_length
              (candle_cv_tame_face_vertices face))
            (Cexp_num 4))
          (Cexp_pair (candle_cv_tame_next_vertex face neighbor)
            (candle_cv_tame_around_keys vertex rest))
          (candle_cv_tame_around_keys vertex rest))))`;;

let candle_cv_tame_remove_key_def = define
 `(candle_cv_tame_remove_key key (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_remove_key key (Cexp_pair entry rest) =
     Cexp_if (Cexp_eq key (Cexp_fst entry))
       (candle_cv_tame_remove_key key rest)
       (Cexp_pair entry (candle_cv_tame_remove_key key rest)))`;;

let candle_cv_tame_remove_keys_def = define
 `(candle_cv_tame_remove_keys (Cexp_num n) table = table) /\
  (candle_cv_tame_remove_keys (Cexp_pair key rest) table =
     candle_cv_tame_remove_key key
       (candle_cv_tame_remove_keys rest table))`;;

let candle_cv_tame_delete_around_def = new_definition
 `candle_cv_tame_delete_around graph vertex table =
    candle_cv_tame_remove_keys
      (candle_cv_tame_around_keys vertex
        (candle_cv_tame_graph_faces_at_vertex graph vertex))
      table`;;

(* The first argument is list-shaped fuel.  With fuel=table this is exactly   *)
(* AFP ExcessNotAtRec.  Both recursive calls consume one fuel cell, while the *)
(* active table is respectively the tail and deleteAround of the tail.        *)
let candle_cv_tame_excess_not_at_rec_fuel_def = define
 `(candle_cv_tame_excess_not_at_rec_fuel (Cexp_num n) graph table =
     Cexp_num 0) /\
  (candle_cv_tame_excess_not_at_rec_fuel (Cexp_pair token fuel) graph table =
     Cexp_if (Cexp_ispair table)
       (let entry = Cexp_fst table in
        let rest = Cexp_snd table in
        let vertex = Cexp_fst entry in
        let excess = Cexp_snd entry in
        candle_cv_tame_max_num
          (candle_cv_tame_excess_not_at_rec_fuel fuel graph rest)
          (Cexp_add excess
            (candle_cv_tame_excess_not_at_rec_fuel fuel graph
              (candle_cv_tame_delete_around graph vertex rest))))
       (Cexp_num 0))`;;

let candle_cv_tame_excess_not_at_rec_def = new_definition
 `candle_cv_tame_excess_not_at_rec graph table =
    candle_cv_tame_excess_not_at_rec_fuel table graph table`;;

let candle_cv_tame_excess_not_at_def = new_definition
 `candle_cv_tame_excess_not_at graph =
    candle_cv_tame_excess_not_at_rec graph
      (candle_cv_tame_excess_table graph)`;;

let candle_cv_tame_squander_lower_bound_def = new_definition
 `candle_cv_tame_squander_lower_bound graph =
    Cexp_add
      (candle_cv_tame_face_squander_sum
        (candle_cv_tame_graph_finals graph))
      (candle_cv_tame_excess_not_at graph)`;;

let candle_cv_tame_is_tame13a_def = new_definition
 `candle_cv_tame_is_tame13a graph =
    Cexp_less (candle_cv_tame_squander_lower_bound graph)
      candle_cv_tame_squander_target`;;

let candle_cv_tame_filter_polysizes_def = define
 `(candle_cv_tame_filter_polysizes lower_bound (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_filter_polysizes lower_bound (Cexp_pair size rest) =
     Cexp_if
       (Cexp_less
         (Cexp_add lower_bound (candle_cv_tame_squander_face size))
         candle_cv_tame_squander_target)
       (Cexp_pair size
         (candle_cv_tame_filter_polysizes lower_bound rest))
       (candle_cv_tame_filter_polysizes lower_bound rest))`;;

let candle_cv_tame_polysizes_def = new_definition
 `candle_cv_tame_polysizes candidates graph =
    candle_cv_tame_filter_polysizes
      (candle_cv_tame_squander_lower_bound graph) candidates`;;

(* All-variable equations admitted by the verified evaluator. *)

let candle_cv_tame_face_squander_sum_compute = prove
 (`!faces. candle_cv_tame_face_squander_sum faces =
    Cexp_if (Cexp_ispair faces)
      (Cexp_add
        (Cexp_if (candle_cv_tame_face_final (Cexp_fst faces))
          (candle_cv_tame_squander_face
            (candle_cv_tame_list_length
              (candle_cv_tame_face_vertices (Cexp_fst faces))))
          (Cexp_num 0))
        (candle_cv_tame_face_squander_sum (Cexp_snd faces)))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_face_squander_sum_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_all_faces_final_compute = prove
 (`!faces. candle_cv_tame_all_faces_final faces =
    Cexp_if (Cexp_ispair faces)
      (candle_cv_tame_and
        (candle_cv_tame_face_final (Cexp_fst faces))
        (candle_cv_tame_all_faces_final (Cexp_snd faces)))
      candle_cv_tame_true`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_all_faces_final_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_count_final_size_compute = prove
 (`!wanted faces. candle_cv_tame_count_final_size wanted faces =
    Cexp_if (Cexp_ispair faces)
      (Cexp_add
        (Cexp_if
          (candle_cv_tame_and
            (candle_cv_tame_face_final (Cexp_fst faces))
            (Cexp_eq
              (candle_cv_tame_list_length
                (candle_cv_tame_face_vertices (Cexp_fst faces))) wanted))
          (Cexp_num 1) (Cexp_num 0))
        (candle_cv_tame_count_final_size wanted (Cexp_snd faces)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_count_final_size_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_count_final_exceptional_compute = prove
 (`!faces. candle_cv_tame_count_final_exceptional faces =
    Cexp_if (Cexp_ispair faces)
      (Cexp_add
        (Cexp_if (candle_cv_tame_face_exceptional (Cexp_fst faces))
          (Cexp_num 1) (Cexp_num 0))
        (candle_cv_tame_count_final_exceptional (Cexp_snd faces)))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_count_final_exceptional_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_excess_table_aux_compute = prove
 (`!index face_lists. candle_cv_tame_excess_table_aux index face_lists =
    Cexp_if (Cexp_ispair face_lists)
      (let faces = Cexp_fst face_lists in
       let excess = candle_cv_tame_excess_at_faces faces in
       Cexp_if (Cexp_less (Cexp_num 0) excess)
         (Cexp_pair (Cexp_pair index excess)
           (candle_cv_tame_excess_table_aux
             (Cexp_add index (Cexp_num 1)) (Cexp_snd face_lists)))
         (candle_cv_tame_excess_table_aux
           (Cexp_add index (Cexp_num 1)) (Cexp_snd face_lists)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `face_lists:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_excess_table_aux_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let candle_cv_tame_around_keys_compute = prove
 (`!vertex faces. candle_cv_tame_around_keys vertex faces =
    Cexp_if (Cexp_ispair faces)
      (let face = Cexp_fst faces in
       let neighbor = candle_cv_tame_next_vertex face vertex in
       Cexp_pair neighbor
         (Cexp_if
           (Cexp_eq
             (candle_cv_tame_list_length
               (candle_cv_tame_face_vertices face))
             (Cexp_num 4))
           (Cexp_pair (candle_cv_tame_next_vertex face neighbor)
             (candle_cv_tame_around_keys vertex (Cexp_snd faces)))
           (candle_cv_tame_around_keys vertex (Cexp_snd faces))))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_around_keys_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let candle_cv_tame_remove_key_compute = prove
 (`!key table. candle_cv_tame_remove_key key table =
    Cexp_if (Cexp_ispair table)
      (Cexp_if (Cexp_eq key (Cexp_fst (Cexp_fst table)))
        (candle_cv_tame_remove_key key (Cexp_snd table))
        (Cexp_pair (Cexp_fst table)
          (candle_cv_tame_remove_key key (Cexp_snd table))))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `table:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_remove_key_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_remove_keys_compute = prove
 (`!keys table. candle_cv_tame_remove_keys keys table =
    Cexp_if (Cexp_ispair keys)
      (candle_cv_tame_remove_key (Cexp_fst keys)
        (candle_cv_tame_remove_keys (Cexp_snd keys) table))
      table`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `keys:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_remove_keys_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_excess_not_at_rec_fuel_compute = prove
 (`!fuel graph table.
    candle_cv_tame_excess_not_at_rec_fuel fuel graph table =
      Cexp_if (Cexp_ispair fuel)
        (Cexp_if (Cexp_ispair table)
          (let entry = Cexp_fst table in
           let rest = Cexp_snd table in
           let vertex = Cexp_fst entry in
           let excess = Cexp_snd entry in
           candle_cv_tame_max_num
             (candle_cv_tame_excess_not_at_rec_fuel
               (Cexp_snd fuel) graph rest)
             (Cexp_add excess
               (candle_cv_tame_excess_not_at_rec_fuel
                 (Cexp_snd fuel) graph
                 (candle_cv_tame_delete_around graph vertex rest))))
          (Cexp_num 0))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `fuel:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_excess_not_at_rec_fuel_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let candle_cv_tame_filter_polysizes_compute = prove
 (`!lower_bound candidates.
    candle_cv_tame_filter_polysizes lower_bound candidates =
      Cexp_if (Cexp_ispair candidates)
        (Cexp_if
          (Cexp_less
            (Cexp_add lower_bound
              (candle_cv_tame_squander_face (Cexp_fst candidates)))
            candle_cv_tame_squander_target)
          (Cexp_pair (Cexp_fst candidates)
            (candle_cv_tame_filter_polysizes lower_bound
              (Cexp_snd candidates)))
          (candle_cv_tame_filter_polysizes lower_bound
            (Cexp_snd candidates)))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `candidates:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_filter_polysizes_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_scoring_compute_eqs =
  candle_cv_tame_pruning_compute_eqs @
  map SPEC_ALL
   [candle_cv_tame_squander_target_def;
    candle_cv_tame_excess_t_count_def;
    candle_cv_tame_max_num_def;
    candle_cv_tame_squander_face_def;
    candle_cv_tame_squander_vertex_def;
    candle_cv_tame_face_squander_sum_compute;
    candle_cv_tame_all_faces_final_compute;
    candle_cv_tame_count_final_size_compute;
    candle_cv_tame_count_final_exceptional_compute;
    candle_cv_tame_excess_at_type_def;
    candle_cv_tame_excess_at_faces_def;
    candle_cv_tame_excess_at_def;
    candle_cv_tame_excess_table_aux_compute;
    candle_cv_tame_excess_table_def;
    candle_cv_tame_around_keys_compute;
    candle_cv_tame_remove_key_compute;
    candle_cv_tame_remove_keys_compute;
    candle_cv_tame_delete_around_def;
    candle_cv_tame_excess_not_at_rec_fuel_compute;
    candle_cv_tame_excess_not_at_rec_def;
    candle_cv_tame_excess_not_at_def;
    candle_cv_tame_squander_lower_bound_def;
    candle_cv_tame_is_tame13a_def;
    candle_cv_tame_filter_polysizes_compute;
    candle_cv_tame_polysizes_def];;

let candle_cv_tame_scoring_compute tm =
  compute candle_cv_tame_scoring_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_SCORING_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
