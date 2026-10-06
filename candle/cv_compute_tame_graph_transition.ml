(* ========================================================================== *)
(* Faithful reflected next_tame transition for the AFP tame enumerator.       *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The runtime enumerator below implements        *)
(* Enumerator.enumerator rather than relying on a growing collection of       *)
(* captured enumTab slices.  It is composed with score-selected polygon       *)
(* sizes, duplicate-edge filtering, subdivision, Generator.notame pruning,    *)
(* and TameEnum's final is_tame filter.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_scoring.ml";;

module Candle_cv_tame_graph_transition = struct

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;
open Candle_cv_tame_graph_pruning;;
open Candle_cv_tame_graph_scoring;;

(* [0 ..< outer - 1], using the outer face only as a checked length control. *)
let candle_cv_tame_enum_range_aux_def = define
 `(candle_cv_tame_enum_range_aux index (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_range_aux index (Cexp_pair token rest) =
     Cexp_if (Cexp_ispair rest)
       (Cexp_pair index
         (candle_cv_tame_enum_range_aux
           (Cexp_add index (Cexp_num 1)) rest))
       (Cexp_num 0))`;;

let candle_cv_tame_enum_range_def = new_definition
 `candle_cv_tame_enum_range face =
    candle_cv_tame_enum_range_aux (Cexp_num 0)
      (candle_cv_tame_face_vertices face)`;;

(* AFP enumBase: one singleton for every number in the finite range. *)
let candle_cv_tame_enum_base_def = define
 `(candle_cv_tame_enum_base (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_base (Cexp_pair value rest) =
     Cexp_pair (candle_cv_tame_singleton value)
       (candle_cv_tame_enum_base rest))`;;

let candle_cv_tame_enum_suffix_def = define
 `(candle_cv_tame_enum_suffix lower (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_suffix lower (Cexp_pair value rest) =
     Cexp_if (candle_cv_tame_le lower value)
       (Cexp_pair value (candle_cv_tame_enum_suffix lower rest))
       (candle_cv_tame_enum_suffix lower rest))`;;

let candle_cv_tame_enum_append_values_def = define
 `(candle_cv_tame_enum_append_values sequence (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_append_values sequence (Cexp_pair value rest) =
     Cexp_pair
       (candle_cv_tame_list_append sequence
         (candle_cv_tame_singleton value))
       (candle_cv_tame_enum_append_values sequence rest))`;;

(* AFP enumAppend, preserving its nested-list order exactly. *)
let candle_cv_tame_enum_append_def = define
 `(candle_cv_tame_enum_append range (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_append range (Cexp_pair sequence rest) =
     candle_cv_tame_list_append
       (candle_cv_tame_enum_append_values sequence
         (candle_cv_tame_enum_suffix
           (candle_cv_tame_list_last (Cexp_num 0) sequence) range))
       (candle_cv_tame_enum_append range rest))`;;

(* Numeric cval recursion implements (enumAppend ^^ k). *)
let candle_cv_tame_enum_iterate_def = define
 `(candle_cv_tame_enum_iterate (Cexp_num 0) range sequences = sequences) /\
  (candle_cv_tame_enum_iterate (Cexp_num (SUC n)) range sequences =
     candle_cv_tame_enum_iterate (Cexp_num n) range
       (candle_cv_tame_enum_append range sequences)) /\
  (candle_cv_tame_enum_iterate (Cexp_pair x y) range sequences = sequences)`;;

let candle_cv_tame_enum_wrap_def = define
 `(candle_cv_tame_enum_wrap outer_last (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_enum_wrap outer_last (Cexp_pair sequence rest) =
     Cexp_pair
       (Cexp_pair (Cexp_num 0)
         (candle_cv_tame_list_append sequence
           (candle_cv_tame_singleton outer_last)))
       (candle_cv_tame_enum_wrap outer_last rest))`;;

let candle_cv_tame_enumerator_def = new_definition
 `candle_cv_tame_enumerator inner face =
    (let outer = candle_cv_tame_list_length
       (candle_cv_tame_face_vertices face) in
     let range = candle_cv_tame_enum_range face in
     let iterations = Cexp_sub inner (Cexp_num 3) in
     candle_cv_tame_enum_wrap (Cexp_sub outer (Cexp_num 1))
       (candle_cv_tame_enum_iterate iterations range
         (candle_cv_tame_enum_base range)))`;;

(* generatePolygonTame for each score-admissible size. *)
let candle_cv_tame_generate_sizes_def = define
 `(candle_cv_tame_generate_sizes graph face vertex (Cexp_num n) =
     Cexp_num 0) /\
  (candle_cv_tame_generate_sizes graph face vertex (Cexp_pair size rest) =
     candle_cv_tame_list_append
       (candle_cv_tame_filter_notame
         (candle_cv_tame_generate_polygon_from_enum graph face vertex
           (candle_cv_tame_enumerator size face)))
       (candle_cv_tame_generate_sizes graph face vertex rest))`;;

let candle_cv_tame_next_tame0_def = new_definition
 `candle_cv_tame_next_tame0 candidates graph =
    (let nonfinals = candle_cv_tame_graph_nonfinals graph in
     Cexp_if (Cexp_ispair nonfinals)
       (let face = candle_cv_tame_min_face nonfinals in
        let vertex = candle_cv_tame_min_vertex graph
          (candle_cv_tame_face_vertices face) in
        candle_cv_tame_generate_sizes graph face vertex
          (candle_cv_tame_polysizes candidates graph))
       (Cexp_num 0))`;;

(* Final-graph tame predicates used by TameEnum.next_tame. *)
let candle_cv_tame_tame11a_faces_at_def = define
 `(candle_cv_tame_tame11a_faces_at (Cexp_num n) = candle_cv_tame_true) /\
  (candle_cv_tame_tame11a_faces_at (Cexp_pair faces rest) =
     Cexp_if
       (candle_cv_tame_le (Cexp_num 3)
         (candle_cv_tame_list_length faces))
       (candle_cv_tame_tame11a_faces_at rest)
       candle_cv_tame_false)`;;

let candle_cv_tame_tame12o_faces_at_def = define
 `(candle_cv_tame_tame12o_faces_at (Cexp_num n) = candle_cv_tame_true) /\
  (candle_cv_tame_tame12o_faces_at (Cexp_pair faces rest) =
     (let triangles =
        candle_cv_tame_count_final_size (Cexp_num 3) faces in
      let quadrilaterals =
        candle_cv_tame_count_final_size (Cexp_num 4) faces in
      let exceptional =
        candle_cv_tame_count_final_exceptional faces in
      let degree = candle_cv_tame_list_length faces in
      let antecedent =
        candle_cv_tame_and
          (candle_cv_tame_not (Cexp_eq exceptional (Cexp_num 0)))
          (Cexp_eq degree (Cexp_num 6)) in
      Cexp_if antecedent
        (Cexp_if
          (candle_cv_tame_and
            (Cexp_eq triangles (Cexp_num 5))
            (candle_cv_tame_and
              (Cexp_eq quadrilaterals (Cexp_num 0))
              (Cexp_eq exceptional (Cexp_num 1))))
          (candle_cv_tame_tame12o_faces_at rest)
          candle_cv_tame_false)
        (candle_cv_tame_tame12o_faces_at rest)))`;;

let candle_cv_tame_is_tame_def = new_definition
 `candle_cv_tame_is_tame graph =
    (let count = candle_cv_tame_graph_vertex_count graph in
     candle_cv_tame_and
       (candle_cv_tame_and
         (candle_cv_tame_le (Cexp_num 13) count)
         (candle_cv_tame_le count (Cexp_num 15)))
       (candle_cv_tame_and
         (candle_cv_tame_tame11a_faces_at
           (candle_cv_tame_graph_faces_at graph))
         (candle_cv_tame_and
           (candle_cv_tame_tame12o_faces_at
             (candle_cv_tame_graph_faces_at graph))
           (candle_cv_tame_is_tame13a graph))))`;;

let candle_cv_tame_filter_final_tame_def = define
 `(candle_cv_tame_filter_final_tame (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_filter_final_tame (Cexp_pair graph rest) =
     Cexp_if
       (candle_cv_tame_and (candle_cv_tame_graph_final graph)
         (candle_cv_tame_not (candle_cv_tame_is_tame graph)))
       (candle_cv_tame_filter_final_tame rest)
       (Cexp_pair graph (candle_cv_tame_filter_final_tame rest)))`;;

let candle_cv_tame_next_tame_def = new_definition
 `candle_cv_tame_next_tame candidates graph =
    candle_cv_tame_filter_final_tame
      (candle_cv_tame_next_tame0 candidates graph)`;;

(* All-variable equations admitted by the verified evaluator. *)

let candle_cv_tame_enum_range_aux_compute = prove
 (`!index controls. candle_cv_tame_enum_range_aux index controls =
    Cexp_if (Cexp_ispair controls)
      (Cexp_if (Cexp_ispair (Cexp_snd controls))
        (Cexp_pair index
          (candle_cv_tame_enum_range_aux
            (Cexp_add index (Cexp_num 1)) (Cexp_snd controls)))
        (Cexp_num 0))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `controls:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_range_aux_def; cexp_if_def;
              cexp_ispair_def; cexp_snd_def]);;

let candle_cv_tame_enum_base_compute = prove
 (`!range. candle_cv_tame_enum_base range =
    Cexp_if (Cexp_ispair range)
      (Cexp_pair (candle_cv_tame_singleton (Cexp_fst range))
        (candle_cv_tame_enum_base (Cexp_snd range)))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `range:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_base_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_enum_suffix_compute = prove
 (`!lower range. candle_cv_tame_enum_suffix lower range =
    Cexp_if (Cexp_ispair range)
      (Cexp_if (candle_cv_tame_le lower (Cexp_fst range))
        (Cexp_pair (Cexp_fst range)
          (candle_cv_tame_enum_suffix lower (Cexp_snd range)))
        (candle_cv_tame_enum_suffix lower (Cexp_snd range)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `range:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_suffix_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_enum_append_values_compute = prove
 (`!sequence values. candle_cv_tame_enum_append_values sequence values =
    Cexp_if (Cexp_ispair values)
      (Cexp_pair
        (candle_cv_tame_list_append sequence
          (candle_cv_tame_singleton (Cexp_fst values)))
        (candle_cv_tame_enum_append_values sequence (Cexp_snd values)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `values:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_append_values_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_enum_append_compute = prove
 (`!range sequences. candle_cv_tame_enum_append range sequences =
    Cexp_if (Cexp_ispair sequences)
      (candle_cv_tame_list_append
        (candle_cv_tame_enum_append_values (Cexp_fst sequences)
          (candle_cv_tame_enum_suffix
            (candle_cv_tame_list_last (Cexp_num 0) (Cexp_fst sequences))
            range))
        (candle_cv_tame_enum_append range (Cexp_snd sequences)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `sequences:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_append_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_enum_iterate_compute = prove
 (`!iterations range sequences.
    candle_cv_tame_enum_iterate iterations range sequences =
      Cexp_if (Cexp_ispair iterations) sequences
        (Cexp_if (Cexp_eq iterations (Cexp_num 0)) sequences
          (candle_cv_tame_enum_iterate
            (Cexp_sub iterations (Cexp_num 1)) range
            (candle_cv_tame_enum_append range sequences)))`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `iterations:cval` (cases "cval")) THENL
   [MP_TAC (SPEC `a:num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `n:num` SUBST1_TAC)) THEN
    REWRITE_TAC[candle_cv_tame_enum_iterate_def; cexp_if_def;
                cexp_ispair_def; cexp_eq_def; cexp_sub_def;
                injectivity "cval"; injectivity "num"; NOT_SUC;
                ARITH_RULE `SUC n - 1 = n`];
    REWRITE_TAC[candle_cv_tame_enum_iterate_def; cexp_if_def;
                cexp_ispair_def]]);;

let candle_cv_tame_enum_wrap_compute = prove
 (`!outer_last sequences. candle_cv_tame_enum_wrap outer_last sequences =
    Cexp_if (Cexp_ispair sequences)
      (Cexp_pair
        (Cexp_pair (Cexp_num 0)
          (candle_cv_tame_list_append (Cexp_fst sequences)
            (candle_cv_tame_singleton outer_last)))
        (candle_cv_tame_enum_wrap outer_last (Cexp_snd sequences)))
      (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `sequences:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_enum_wrap_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_generate_sizes_compute = prove
 (`!graph face vertex sizes.
    candle_cv_tame_generate_sizes graph face vertex sizes =
      Cexp_if (Cexp_ispair sizes)
        (candle_cv_tame_list_append
          (candle_cv_tame_filter_notame
            (candle_cv_tame_generate_polygon_from_enum graph face vertex
              (candle_cv_tame_enumerator (Cexp_fst sizes) face)))
          (candle_cv_tame_generate_sizes graph face vertex
            (Cexp_snd sizes)))
        (Cexp_num 0)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC (SPEC `sizes:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_generate_sizes_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_tame11a_faces_at_compute = prove
 (`!face_lists. candle_cv_tame_tame11a_faces_at face_lists =
    Cexp_if (Cexp_ispair face_lists)
      (Cexp_if
        (candle_cv_tame_le (Cexp_num 3)
          (candle_cv_tame_list_length (Cexp_fst face_lists)))
        (candle_cv_tame_tame11a_faces_at (Cexp_snd face_lists))
        candle_cv_tame_false)
      candle_cv_tame_true`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `face_lists:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_tame11a_faces_at_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_tame12o_faces_at_compute = prove
 (`!face_lists. candle_cv_tame_tame12o_faces_at face_lists =
    Cexp_if (Cexp_ispair face_lists)
      (let faces = Cexp_fst face_lists in
       let triangles =
         candle_cv_tame_count_final_size (Cexp_num 3) faces in
       let quadrilaterals =
         candle_cv_tame_count_final_size (Cexp_num 4) faces in
       let exceptional =
         candle_cv_tame_count_final_exceptional faces in
       let degree = candle_cv_tame_list_length faces in
       let antecedent =
         candle_cv_tame_and
           (candle_cv_tame_not (Cexp_eq exceptional (Cexp_num 0)))
           (Cexp_eq degree (Cexp_num 6)) in
       Cexp_if antecedent
         (Cexp_if
           (candle_cv_tame_and
             (Cexp_eq triangles (Cexp_num 5))
             (candle_cv_tame_and
               (Cexp_eq quadrilaterals (Cexp_num 0))
               (Cexp_eq exceptional (Cexp_num 1))))
           (candle_cv_tame_tame12o_faces_at (Cexp_snd face_lists))
           candle_cv_tame_false)
         (candle_cv_tame_tame12o_faces_at (Cexp_snd face_lists)))
      candle_cv_tame_true`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `face_lists:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_tame12o_faces_at_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let candle_cv_tame_filter_final_tame_compute = prove
 (`!graphs. candle_cv_tame_filter_final_tame graphs =
    Cexp_if (Cexp_ispair graphs)
      (Cexp_if
        (candle_cv_tame_and
          (candle_cv_tame_graph_final (Cexp_fst graphs))
          (candle_cv_tame_not
            (candle_cv_tame_is_tame (Cexp_fst graphs))))
        (candle_cv_tame_filter_final_tame (Cexp_snd graphs))
        (Cexp_pair (Cexp_fst graphs)
          (candle_cv_tame_filter_final_tame (Cexp_snd graphs))))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `graphs:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_tame_filter_final_tame_def; cexp_if_def;
              cexp_ispair_def; cexp_fst_def; cexp_snd_def]);;

let candle_cv_tame_transition_compute_eqs =
  candle_cv_tame_scoring_compute_eqs @
  map SPEC_ALL
   [candle_cv_tame_enum_range_aux_compute;
    candle_cv_tame_enum_range_def;
    candle_cv_tame_enum_base_compute;
    candle_cv_tame_enum_suffix_compute;
    candle_cv_tame_enum_append_values_compute;
    candle_cv_tame_enum_append_compute;
    candle_cv_tame_enum_iterate_compute;
    candle_cv_tame_enum_wrap_compute;
    candle_cv_tame_enumerator_def;
    candle_cv_tame_generate_sizes_compute;
    candle_cv_tame_next_tame0_def;
    candle_cv_tame_tame11a_faces_at_compute;
    candle_cv_tame_tame12o_faces_at_compute;
    candle_cv_tame_is_tame_def;
    candle_cv_tame_filter_final_tame_compute;
    candle_cv_tame_next_tame_def];;

let candle_cv_tame_transition_compute tm =
  compute candle_cv_tame_transition_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_TRANSITION_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
