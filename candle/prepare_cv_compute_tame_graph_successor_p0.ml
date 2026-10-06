(* Stable prepared state for host-timed p=0 successor throughput probes. *)

needs "candle/test_cv_compute_tame_graph_enumerator_seed.ml";;
needs "candle/cv_compute_tame_graph_successor.ml";;

open Candle_cv_tame_graph_enumerator_core;;
open Candle_cv_tame_graph_successor;;

let candle_cv_tame_p0_prepared_enum_002 =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 0)
    (Cexp_pair (Cexp_num 2) (Cexp_num 0)))`;;

let candle_cv_tame_p0_prepared_enum_012 =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 1)
    (Cexp_pair (Cexp_num 2) (Cexp_num 0)))`;;

let candle_cv_tame_p0_prepared_enumeration =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_prepared_enum_002),
    mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_prepared_enum_012),
      `Cexp_num 0`));;

let candle_cv_tame_p0_prepared_workload =
  list_mk_comb
    (`candle_cv_tame_generate_polygon_from_enum`,
     [candle_cv_tame_p0_expected;
      candle_cv_tame_p0_open_face;
      `Cexp_num 2`;
      candle_cv_tame_p0_prepared_enumeration]);;

let _ = print_endline
  "CANDLE_CV_TAME_P0_PREPARED_READY enum=2 DEVELOPMENT_NON_RELEASE";;

