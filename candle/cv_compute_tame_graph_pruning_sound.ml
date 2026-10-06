(* ========================================================================== *)
(* Logical meaning of the reflected AFP Generator.notame decision.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The theorem at the end covers every typed      *)
(* graph encoding at this boundary, rather than only the focused fixtures.    *)
(* ========================================================================== *)

needs "candle/cv_compute_tame_graph_pruning.ml";;
needs "candle/cv_compute_tame_graph_data_sound.ml";;

module Candle_cv_tame_graph_pruning_sound = struct

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_pruning;;
open Candle_cv_flyspeck_lists_core;;
open Candle_cv_tame_graph_data_sound;;

let candle_tame_cv_pruning_face_def = new_definition
 `candle_tame_cv_pruning_face (face:(num list)#bool) =
    Cexp_pair (candle_cv_num_list (FST face))
      (candle_tame_cv_bool (SND face))`;;

let candle_tame_cv_pruning_faces_def =
  new_recursive_definition list_RECURSION
   `(candle_tame_cv_pruning_faces ([]:((num list)#bool)list) = Cexp_num 0) /\
    (candle_tame_cv_pruning_faces (CONS face rest) =
       Cexp_pair (candle_tame_cv_pruning_face face)
         (candle_tame_cv_pruning_faces rest))`;;

let candle_tame_cv_pruning_faces_at_def =
  new_recursive_definition list_RECURSION
   `(candle_tame_cv_pruning_faces_at
       ([]:(((num list)#bool)list)list) = Cexp_num 0) /\
    (candle_tame_cv_pruning_faces_at (CONS vertex_faces rest) =
       Cexp_pair (candle_tame_cv_pruning_faces vertex_faces)
         (candle_tame_cv_pruning_faces_at rest))`;;

let candle_tame_cv_pruning_graph_def = new_definition
 `candle_tame_cv_pruning_graph vertex_count face_lists =
    Cexp_pair (Cexp_num 0)
      (Cexp_pair (Cexp_num vertex_count)
        (Cexp_pair (candle_tame_cv_pruning_faces_at face_lists)
          (Cexp_num 0)))`;;

let candle_tame_face_exceptional_logical_def = new_definition
 `candle_tame_face_exceptional_logical (face:(num list)#bool) <=>
    SND face /\ 5 <= LENGTH (FST face)`;;

let candle_tame_faces_except_count_logical_def =
  new_recursive_definition list_RECURSION
   `(candle_tame_faces_except_count_logical
       ([]:((num list)#bool)list) = 0) /\
    (candle_tame_faces_except_count_logical (CONS face rest) =
       (if candle_tame_face_exceptional_logical face then 1 else 0) +
       candle_tame_faces_except_count_logical rest)`;;

let candle_tame_tame11b_faces_at_logical_def = define
 `(candle_tame_tame11b_faces_at_logical
     ([]:(((num list)#bool)list)list) = T) /\
  (candle_tame_tame11b_faces_at_logical (CONS vertex_faces rest) =
     if LENGTH vertex_faces <=
          (if candle_tame_faces_except_count_logical vertex_faces = 0
           then 7 else 6)
     then candle_tame_tame11b_faces_at_logical rest
     else F)`;;

let candle_tame_notame_logical_def = new_definition
 `candle_tame_notame_logical vertex_count face_lists <=>
    ~(vertex_count <= 15 /\
      candle_tame_tame11b_faces_at_logical face_lists)`;;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND definitions_ready";;

let candle_tame_exact_match_tac theorem (assumptions,goal as state) =
  ACCEPT_TAC (PART_MATCH I (SPEC_ALL theorem) goal) state;;

let candle_tame_cv_not_correct = prove
 (`!value.
     candle_cv_tame_not (candle_tame_cv_bool value) =
     candle_tame_cv_bool (~value)`,
  GEN_TAC THEN BOOL_CASES_TAC `value:bool` THEN
  REWRITE_TAC[candle_tame_cv_bool_def; candle_cv_tame_not_def;
              candle_cv_tame_false_def; candle_cv_tame_true_def;
              cexp_if_def; ARITH_RULE `1 = SUC 0`]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND not_correct";;

let candle_tame_cv_and_correct = prove
 (`!left right.
     candle_cv_tame_and
       (candle_tame_cv_bool left) (candle_tame_cv_bool right) =
     candle_tame_cv_bool (left /\ right)`,
  REPEAT GEN_TAC THEN
  BOOL_CASES_TAC `left:bool` THEN BOOL_CASES_TAC `right:bool` THEN
  REWRITE_TAC[candle_tame_cv_bool_def; candle_cv_tame_and_def;
              candle_cv_tame_false_def; candle_cv_tame_true_def;
              cexp_if_def; ARITH_RULE `1 = SUC 0`]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND and_correct";;

let candle_tame_cv_if_bool_false_correct = prove
 (`!condition value.
     (if condition then candle_tame_cv_bool value
      else candle_cv_tame_false) =
     candle_tame_cv_bool (if condition then value else F)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `condition:bool` THEN
  REWRITE_TAC[candle_tame_cv_bool_def; candle_cv_tame_false_def]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND if_bool_correct";;

let candle_tame_cv_num_le_correct = prove
 (`!left right.
     candle_cv_tame_le (Cexp_num left) (Cexp_num right) =
     candle_tame_cv_bool (left <= right)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_cv_tame_le_def; candle_tame_cv_num_less_correct;
              candle_tame_cv_not_correct] THEN
  AP_TERM_TAC THEN ARITH_TAC);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND le_correct";;

let candle_tame_cv_le_if_bool_false_correct = prove
 (`!value left right.
     Cexp_if
       (candle_cv_tame_le (Cexp_num left) (Cexp_num right))
       (candle_tame_cv_bool value) candle_cv_tame_false =
     candle_tame_cv_bool (if left <= right then value else F)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[candle_tame_cv_num_le_correct] THEN
  REWRITE_TAC[candle_tame_cv_if_correct] THEN
  MATCH_ACCEPT_TAC candle_tame_cv_if_bool_false_correct);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND le_if_bool_correct";;

let candle_tame_cv_num_list_length_correct = prove
 (`!values:num list.
     candle_cv_tame_list_length (candle_cv_num_list values) =
     Cexp_num (LENGTH values)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_list_def;
                  candle_cv_tame_list_length_def;
                  CONJUNCT1 cexp_add_def;
                  LENGTH; ADD_CLAUSES;
                  ARITH_RULE `1 + n = SUC n`]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND length_correct";;

let candle_tame_cv_pruning_faces_length_correct = prove
 (`!faces:((num list)#bool)list.
     candle_cv_tame_list_length (candle_tame_cv_pruning_faces faces) =
     Cexp_num (LENGTH faces)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_tame_cv_pruning_faces_def;
                  candle_cv_tame_list_length_def;
                  CONJUNCT1 cexp_add_def;
                  LENGTH; ADD_CLAUSES;
                  ARITH_RULE `1 + n = SUC n`]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND faces_length_correct";;

let candle_tame_cv_pruning_face_vertices_correct = prove
 (`!face:(num list)#bool.
     candle_cv_tame_face_vertices (candle_tame_cv_pruning_face face) =
     candle_cv_num_list (FST face)`,
  REWRITE_TAC[candle_tame_cv_pruning_face_def;
              candle_cv_tame_face_vertices_def; cexp_fst_def]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND face_vertices_correct";;

let candle_tame_cv_pruning_face_final_correct = prove
 (`!face:(num list)#bool.
     candle_cv_tame_face_final (candle_tame_cv_pruning_face face) =
     candle_tame_cv_bool (SND face)`,
  REWRITE_TAC[candle_tame_cv_pruning_face_def;
              candle_cv_tame_face_final_def; cexp_snd_def]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND face_final_correct";;

let candle_tame_cv_face_exceptional_correct = prove
 (`!face:(num list)#bool.
     candle_cv_tame_face_exceptional
       (candle_tame_cv_pruning_face face) =
     candle_tame_cv_bool (candle_tame_face_exceptional_logical face)`,
  REWRITE_TAC[candle_cv_tame_face_exceptional_def;
              candle_tame_face_exceptional_logical_def;
              candle_tame_cv_pruning_face_vertices_correct;
              candle_tame_cv_pruning_face_final_correct;
              candle_tame_cv_num_list_length_correct;
              candle_tame_cv_num_le_correct;
              candle_tame_cv_and_correct]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND exceptional_correct";;

let candle_tame_cv_faces_except_count_correct = prove
 (`!faces:((num list)#bool)list.
     candle_cv_tame_faces_except_count
       (candle_tame_cv_pruning_faces faces) =
     Cexp_num (candle_tame_faces_except_count_logical faces)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[candle_tame_cv_pruning_faces_def;
                candle_cv_tame_faces_except_count_def;
                candle_tame_faces_except_count_logical_def];
    ASM_REWRITE_TAC[candle_tame_cv_pruning_faces_def;
                    candle_cv_tame_faces_except_count_def;
                    candle_tame_faces_except_count_logical_def;
                    candle_tame_cv_face_exceptional_correct;
                    candle_tame_cv_if_correct;
                    CONJUNCT1 cexp_add_def] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[candle_tame_cv_bool_def;
                                      cexp_if_def;
                                      CONJUNCT1 cexp_add_def;
                                      ARITH_RULE `1 + n = SUC n`;
                                      ADD_CLAUSES]]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND except_count_correct";;

let candle_tame_cv_tame11b_faces_at_correct = prove
 (`!face_lists:(((num list)#bool)list)list.
     candle_cv_tame_tame11b_faces_at
       (candle_tame_cv_pruning_faces_at face_lists) =
     candle_tame_cv_bool
       (candle_tame_tame11b_faces_at_logical face_lists)`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[candle_tame_cv_pruning_faces_at_def;
                candle_cv_tame_tame11b_faces_at_def;
                candle_tame_tame11b_faces_at_logical_def;
                candle_tame_cv_bool_def;
                candle_cv_tame_true_def;
                ARITH_RULE `1 = SUC 0`];
    MAP_EVERY X_GEN_TAC
      [`h:((num list)#bool)list`;
       `t:(((num list)#bool)list)list`] THEN
    DISCH_TAC THEN
    ASM_REWRITE_TAC[candle_tame_cv_pruning_faces_at_def;
                    candle_cv_tame_tame11b_faces_at_def;
                    candle_tame_tame11b_faces_at_logical_def;
                    candle_tame_cv_faces_except_count_correct;
                    candle_tame_cv_pruning_faces_length_correct;
                    candle_tame_cv_num_eq_correct;
                    LET_DEF; LET_END_DEF] THEN
    ASM_CASES_TAC
      `candle_tame_faces_except_count_logical h = 0` THEN
    ASM_REWRITE_TAC[candle_tame_cv_if_correct] THEN
    candle_tame_exact_match_tac candle_tame_cv_le_if_bool_false_correct]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND tame11b_correct";;

let candle_tame_cv_pruning_graph_selectors = prove
 (`(!vertex_count face_lists.
      candle_cv_tame_graph_vertex_count
        (candle_tame_cv_pruning_graph vertex_count face_lists) =
      Cexp_num vertex_count) /\
   (!vertex_count face_lists.
      candle_cv_tame_graph_faces_at
        (candle_tame_cv_pruning_graph vertex_count face_lists) =
      candle_tame_cv_pruning_faces_at face_lists)`,
  REWRITE_TAC[candle_tame_cv_pruning_graph_def;
              candle_cv_tame_graph_vertex_count_def;
              candle_cv_tame_graph_faces_at_def;
              cexp_fst_def; cexp_snd_def]);;

let _ = print_endline "CANDLE_CV_TAME_PRUNING_SOUND selectors_correct";;

let candle_tame_cv_notame_correct = prove
 (`!vertex_count face_lists.
     candle_cv_tame_notame
       (candle_tame_cv_pruning_graph vertex_count face_lists) =
     candle_tame_cv_bool
       (candle_tame_notame_logical vertex_count face_lists)`,
  REWRITE_TAC[candle_cv_tame_notame_def;
              candle_tame_notame_logical_def;
              candle_tame_cv_pruning_graph_selectors;
              candle_tame_cv_tame11b_faces_at_correct;
              candle_tame_cv_num_le_correct;
              candle_tame_cv_and_correct;
              candle_tame_cv_not_correct]);;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_PRUNING_SOUND_OK DEVELOPMENT_NON_RELEASE";;

end;;
