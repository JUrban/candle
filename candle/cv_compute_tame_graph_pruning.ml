(* ========================================================================== *)
(* Faithful reflected first-stage pruning for the AFP tame enumerator.        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is exactly Generator.notame: reject a     *)
(* graph when countVertices <= 15 and tame11b do not both hold.  For each     *)
(* vertex, tame11b bounds the face degree by 7 when there is no final face of  *)
(* size at least 5, and by 6 otherwise.                                       *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_successor.ml";;

module Candle_cv_tame_graph_pruning = struct

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;

let candle_cv_tame_face_exceptional_def = new_definition
 `candle_cv_tame_face_exceptional face =
    candle_cv_tame_and
      (candle_cv_tame_face_final face)
      (candle_cv_tame_le (Cexp_num 5)
        (candle_cv_tame_list_length
          (candle_cv_tame_face_vertices face)))`;;

let candle_cv_tame_faces_except_count_def = define
 `(candle_cv_tame_faces_except_count (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_faces_except_count (Cexp_pair face rest) =
     Cexp_add
       (Cexp_if (candle_cv_tame_face_exceptional face)
         (Cexp_num 1) (Cexp_num 0))
       (candle_cv_tame_faces_except_count rest))`;;

let candle_cv_tame_tame11b_faces_at_def = define
 `(candle_cv_tame_tame11b_faces_at (Cexp_num n) = candle_cv_tame_true) /\
  (candle_cv_tame_tame11b_faces_at (Cexp_pair vertex_faces rest) =
     (let exception_count =
        candle_cv_tame_faces_except_count vertex_faces in
      let maximum_degree =
        Cexp_if (Cexp_eq exception_count (Cexp_num 0))
          (Cexp_num 7) (Cexp_num 6) in
      Cexp_if
        (candle_cv_tame_le
          (candle_cv_tame_list_length vertex_faces) maximum_degree)
        (candle_cv_tame_tame11b_faces_at rest)
        candle_cv_tame_false))`;;

let candle_cv_tame_notame_def = new_definition
 `candle_cv_tame_notame graph =
    candle_cv_tame_not
      (candle_cv_tame_and
        (candle_cv_tame_le
          (candle_cv_tame_graph_vertex_count graph) (Cexp_num 15))
        (candle_cv_tame_tame11b_faces_at
          (candle_cv_tame_graph_faces_at graph)))`;;

let candle_cv_tame_filter_notame_def = define
 `(candle_cv_tame_filter_notame (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_tame_filter_notame (Cexp_pair graph rest) =
     Cexp_if (candle_cv_tame_notame graph)
       (candle_cv_tame_filter_notame rest)
       (Cexp_pair graph (candle_cv_tame_filter_notame rest)))`;;

(* All-variable equations admitted by the verified evaluator. *)

let candle_cv_tame_faces_except_count_compute = prove
 (`!faces. candle_cv_tame_faces_except_count faces =
    Cexp_if (Cexp_ispair faces)
      (Cexp_add
        (Cexp_if
          (candle_cv_tame_face_exceptional (Cexp_fst faces))
          (Cexp_num 1) (Cexp_num 0))
        (candle_cv_tame_faces_except_count (Cexp_snd faces)))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `faces:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_faces_except_count_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let candle_cv_tame_tame11b_faces_at_compute = prove
 (`!face_lists. candle_cv_tame_tame11b_faces_at face_lists =
    Cexp_if (Cexp_ispair face_lists)
      (let vertex_faces = Cexp_fst face_lists in
       let exception_count =
         candle_cv_tame_faces_except_count vertex_faces in
       let maximum_degree =
         Cexp_if (Cexp_eq exception_count (Cexp_num 0))
           (Cexp_num 7) (Cexp_num 6) in
       Cexp_if
         (candle_cv_tame_le
           (candle_cv_tame_list_length vertex_faces) maximum_degree)
         (candle_cv_tame_tame11b_faces_at (Cexp_snd face_lists))
         candle_cv_tame_false)
      candle_cv_tame_true`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `face_lists:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_tame11b_faces_at_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def @
     [LET_DEF; LET_END_DEF]));;

let candle_cv_tame_filter_notame_compute = prove
 (`!graphs. candle_cv_tame_filter_notame graphs =
    Cexp_if (Cexp_ispair graphs)
      (Cexp_if (candle_cv_tame_notame (Cexp_fst graphs))
        (candle_cv_tame_filter_notame (Cexp_snd graphs))
        (Cexp_pair (Cexp_fst graphs)
          (candle_cv_tame_filter_notame (Cexp_snd graphs))))
      (Cexp_num 0)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `graphs:cval` (cases "cval")) THEN
  REWRITE_TAC
    (CONJUNCTS candle_cv_tame_filter_notame_def @
     CONJUNCTS cexp_if_def @ CONJUNCTS cexp_ispair_def @
     CONJUNCTS cexp_fst_def @ CONJUNCTS cexp_snd_def));;

let candle_cv_tame_pruning_compute_eqs =
  candle_cv_tame_successor_compute_eqs @
  map SPEC_ALL
   [candle_cv_tame_face_exceptional_def;
    candle_cv_tame_faces_except_count_compute;
    candle_cv_tame_tame11b_faces_at_compute;
    candle_cv_tame_notame_def;
    candle_cv_tame_filter_notame_compute];;

let candle_cv_tame_pruning_compute tm =
  compute candle_cv_tame_pruning_compute_eqs tm;;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_PRUNING_CORE_OK DEVELOPMENT_NON_RELEASE";;

end;;
