(* Fresh-base smoke test for the proof-producing Flyspeck list cval core. *)

needs "candle/compute.ml";;
needs "candle/cv_compute_flyspeck_lists_core.ml";;

open Candle_cv_flyspeck_lists_core;;

let candle_cv_core_smoke = compute candle_cv_list_of_faces_compute_eqs
 `candle_cv_list_of_faces
    (Cexp_pair
      (Cexp_pair (Cexp_num 1)
        (Cexp_pair (Cexp_num 2) (Cexp_num 0)))
      (Cexp_num 0))`;;

let candle_cv_core_smoke_expected =
 `candle_cv_list_of_faces
    (Cexp_pair
      (Cexp_pair (Cexp_num 1)
        (Cexp_pair (Cexp_num 2) (Cexp_num 0)))
      (Cexp_num 0)) =
  Cexp_pair
    (Cexp_pair
      (Cexp_pair (Cexp_num 1) (Cexp_num 2))
      (Cexp_pair
        (Cexp_pair (Cexp_num 2) (Cexp_num 1))
        (Cexp_num 0)))
    (Cexp_num 0)`;;

if not (aconv (concl candle_cv_core_smoke) candle_cv_core_smoke_expected)
then failwith "cv_compute Flyspeck list core smoke mismatch";;
if hyp candle_cv_core_smoke <> []
then failwith "cv_compute Flyspeck list core produced assumptions";;

print_endline "CANDLE_CV_FLYSPECK_LIST_CORE_OK";;
