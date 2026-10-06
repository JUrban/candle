(* Fresh-base checks for the reflected tame-graph data boundary. *)

needs "candle/cv_compute_tame_graph_data.ml";;

open Candle_cv_tame_graph_data;;

let candle_tame_assert_result label expected theorem =
  let actual = rand (concl theorem) in
  if not (aconv actual expected) then
    failwith ("tame graph data result mismatch: " ^ label)
  else if hyp theorem <> [] then
    failwith ("tame graph data assumptions: " ^ label)
  else
    print_endline ("CANDLE_CV_TAME_GRAPH_DATA_CASE_OK:" ^ label);;

let candle_tame_valid_graph =
 `Cexp_pair
    (Cexp_pair (Cexp_num 0)
      (Cexp_pair (Cexp_num 1)
        (Cexp_pair (Cexp_num 2) (Cexp_num 0))))
    (Cexp_pair
      (Cexp_pair (Cexp_num 0)
        (Cexp_pair (Cexp_num 2)
          (Cexp_pair (Cexp_num 3) (Cexp_num 0))))
      (Cexp_num 0))`;;

let candle_tame_valid_map =
 `Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 3))
   (Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 2))
    (Cexp_pair (Cexp_pair (Cexp_num 2) (Cexp_num 1))
     (Cexp_pair (Cexp_pair (Cexp_num 3) (Cexp_num 0))
      (Cexp_num 0))))`;;

let candle_tame_compute tm =
  compute candle_cv_tame_graph_data_compute_eqs tm;;

let candle_tame_valid_graph_th = candle_tame_compute
  (mk_comb
    (mk_comb (`candle_cv_tame_nonempty_fgraph_valid`, `Cexp_num 4`),
     candle_tame_valid_graph));;
let _ = candle_tame_assert_result
  "valid_graph" `Cexp_num 1` candle_tame_valid_graph_th;;

let candle_tame_valid_map_th = candle_tame_compute
  (mk_comb
    (mk_comb
      (mk_comb (`candle_cv_tame_vertex_map_valid`, `Cexp_num 4`),
       `Cexp_num 4`),
     candle_tame_valid_map));;
let _ = candle_tame_assert_result
  "valid_map" `Cexp_num 1` candle_tame_valid_map_th;;

let candle_tame_cases =
 ["empty_graph",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4) (Cexp_num 0)`;
  "nonzero_graph_tail",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4)
      (Cexp_pair
        (Cexp_pair (Cexp_num 0)
          (Cexp_pair (Cexp_num 1) (Cexp_num 0)))
        (Cexp_num 7))`;
  "empty_face",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4)
      (Cexp_pair (Cexp_num 0) (Cexp_num 0))`;
  "pair_vertex",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4)
      (Cexp_pair
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 1))
          (Cexp_num 0))
        (Cexp_num 0))`;
  "vertex_out_of_range",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4)
      (Cexp_pair
        (Cexp_pair (Cexp_num 0)
          (Cexp_pair (Cexp_num 4) (Cexp_num 0)))
        (Cexp_num 0))`;
  "duplicate_face_vertex",
   `candle_cv_tame_nonempty_fgraph_valid
      (Cexp_num 4)
      (Cexp_pair
        (Cexp_pair (Cexp_num 0)
          (Cexp_pair (Cexp_num 1)
            (Cexp_pair (Cexp_num 0) (Cexp_num 0))))
        (Cexp_num 0))`;
  "nonzero_map_tail",
   `candle_cv_tame_vertex_map_valid
      (Cexp_num 4) (Cexp_num 4)
      (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 1))
        (Cexp_num 9))`;
  "malformed_map_entry",
   `candle_cv_tame_vertex_map_valid
      (Cexp_num 4) (Cexp_num 4)
      (Cexp_pair (Cexp_num 0) (Cexp_num 0))`;
  "map_source_out_of_range",
   `candle_cv_tame_vertex_map_valid
      (Cexp_num 4) (Cexp_num 4)
      (Cexp_pair (Cexp_pair (Cexp_num 4) (Cexp_num 0))
        (Cexp_num 0))`;
  "duplicate_map_source",
   `candle_cv_tame_vertex_map_valid
      (Cexp_num 4) (Cexp_num 4)
      (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0))
        (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 1))
          (Cexp_num 0)))`;
  "duplicate_map_target",
   `candle_cv_tame_vertex_map_valid
      (Cexp_num 4) (Cexp_num 4)
      (Cexp_pair (Cexp_pair (Cexp_num 0) (Cexp_num 0))
        (Cexp_pair (Cexp_pair (Cexp_num 1) (Cexp_num 0))
          (Cexp_num 0)))`];;

let _ = do_list
  (fun (label,tm) ->
    candle_tame_assert_result label `Cexp_num 0` (candle_tame_compute tm))
  candle_tame_cases;;

let _ =
  ignore candle_cv_tame_face_roundtrip;
  ignore candle_cv_tame_fgraph_roundtrip;
  ignore candle_cv_tame_vertex_map_roundtrip;
  ignore candle_cv_tame_face_injective;
  ignore candle_cv_tame_fgraph_injective;
  ignore candle_cv_tame_vertex_map_injective;
  print_endline "CANDLE_CV_TAME_GRAPH_DATA_TEST_OK";;
