(* Fresh-base kernel checks for tame-graph data-validator correspondence. *)

let candle_tame_graph_data_sound_axioms_before = axioms ();;

needs "candle/cv_compute_tame_graph_data_sound.ml";;

open Candle_cv_tame_graph_data_sound;;

let candle_tame_graph_data_sound_theorems =
 [candle_cv_tame_num_member_correct;
  candle_cv_tame_num_list_valid_aux_correct;
  candle_cv_tame_num_list_valid_correct;
  candle_cv_tame_fgraph_valid_correct;
  candle_cv_tame_nonempty_fgraph_valid_correct;
  candle_cv_tame_vertex_map_valid_aux_correct;
  candle_cv_tame_vertex_map_valid_correct];;

if not (List.for_all (fun theorem -> hyp theorem = [])
          candle_tame_graph_data_sound_theorems) then
  failwith "tame graph data soundness: theorem has assumptions";;

let candle_tame_graph_data_sound_axioms_after = axioms ();;

if length candle_tame_graph_data_sound_axioms_after <>
     length candle_tame_graph_data_sound_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_tame_graph_data_sound_axioms_before)
     candle_tame_graph_data_sound_axioms_after) then
  failwith "tame graph data soundness: changed the global axiom set";;

print_endline
  "CANDLE_CV_TAME_GRAPH_DATA_SOUND_TEST_OK assumptions=0 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
