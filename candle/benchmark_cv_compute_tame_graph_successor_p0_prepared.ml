(* Run only after prepare_cv_compute_tame_graph_successor_p0.ml is ready. *)

needs "candle/prepare_cv_compute_tame_graph_successor_p0.ml";;

let rec candle_cv_tame_p0_host_timed_repeat count =
  if count = 0 then ()
  else
    let _ = Candle_cv_tame_graph_successor.candle_cv_tame_successor_compute
      candle_cv_tame_p0_prepared_workload in
    candle_cv_tame_p0_host_timed_repeat (count - 1);;

let candle_cv_tame_p0_host_timed_count = 1000;;
let _ = candle_cv_tame_p0_host_timed_repeat
  candle_cv_tame_p0_host_timed_count;;

let _ = print_endline
  "CANDLE_CV_TAME_P0_PREPARED_BENCHMARK_OK repeats=1000 batches=1000 children=2000 DEVELOPMENT_NON_RELEASE";;
