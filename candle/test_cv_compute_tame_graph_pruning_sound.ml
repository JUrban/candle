(* Fresh-kernel assumption and axiom checks for typed notame correspondence. *)

let candle_cv_tame_pruning_sound_axioms_before = axioms ();;

needs "candle/cv_compute_tame_graph_pruning_sound.ml";;

open Candle_cv_tame_graph_pruning_sound;;

let candle_cv_tame_pruning_sound_checked_theorems =
 [candle_tame_cv_not_correct;
  candle_tame_cv_and_correct;
  candle_tame_cv_if_bool_false_correct;
  candle_tame_cv_num_le_correct;
  candle_tame_cv_le_if_bool_false_correct;
  candle_tame_cv_num_list_length_correct;
  candle_tame_cv_pruning_faces_length_correct;
  candle_tame_cv_pruning_face_vertices_correct;
  candle_tame_cv_pruning_face_final_correct;
  candle_tame_cv_face_exceptional_correct;
  candle_tame_cv_faces_except_count_correct;
  candle_tame_cv_tame11b_faces_at_correct;
  CONJUNCT1 candle_tame_cv_pruning_graph_selectors;
  CONJUNCT2 candle_tame_cv_pruning_graph_selectors;
  candle_tame_cv_notame_correct];;

if not (List.for_all
  (fun theorem -> hyp theorem = [])
  candle_cv_tame_pruning_sound_checked_theorems) then
  failwith "tame pruning soundness: theorem has assumptions";;

let candle_cv_tame_pruning_sound_axioms_after = axioms ();;

if length candle_cv_tame_pruning_sound_axioms_after <>
     length candle_cv_tame_pruning_sound_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_pruning_sound_axioms_before)
     candle_cv_tame_pruning_sound_axioms_after) then
  failwith "tame pruning soundness: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_PRUNING_SOUND_TEST_OK theorems=15 assumptions=0 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
