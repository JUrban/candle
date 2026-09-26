(* ========================================================================== *)
(* Genuine Flyspeck split tree from one-verdict fixed-scale batch leaves.    *)
(* ========================================================================== *)

needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_fixed_proved_batch.ml";;
needs "candle/test_cv_compute_polynomial_expr_flyspeck_real_leaf_jet_certificate.ml";;

open Candle_cv_real_flyspeck_leaf_jet_batch_test;;
open Candle_cv_real_flyspeck_leaf_fixed_proved_batch_test;;
open Candle_cv_real_flyspeck_leaf_jet_certificate_test;;

module Candle_cv_real_flyspeck_leaf_fixed_proved_certificate_test = struct

let candle_real_fixed_proved_certificate_leaf_passes =
  map2 candle_real_jet_certificate_leaf_pass
    candle_real_fixed_proved_batch_theorems
    candle_real_jet_batch_box_sources;;

let rec candle_real_fixed_proved_certificate_assemble tree =
  match tree with
  | Candle_real_jet_leaf index ->
      List.nth candle_real_fixed_proved_certificate_leaf_passes index
  | Candle_real_jet_glue (index,left,right) ->
      let left_th = candle_real_fixed_proved_certificate_assemble left in
      let right_th = candle_real_fixed_proved_certificate_assemble right in
      candle_real_jet_certificate_glue index left_th right_th;;

let candle_real_fixed_proved_certificate_root_theorem =
  candle_real_fixed_proved_certificate_assemble
    candle_real_jet_certificate_tree;;

let candle_real_fixed_proved_certificate_root_function,
    candle_real_fixed_proved_certificate_root_lower,
    candle_real_fixed_proved_certificate_root_upper =
  candle_real_jet_certificate_dest_pass
    candle_real_fixed_proved_certificate_root_theorem;;

if length candle_real_fixed_proved_certificate_leaf_passes <> 16 ||
   candle_real_jet_certificate_leaf_indices <> (0--15) ||
   candle_real_jet_certificate_glue_count <> 15 ||
   hyp candle_real_fixed_proved_certificate_root_theorem <> [] ||
   not
     (aconv candle_real_fixed_proved_certificate_root_function
        candle_real_jet_certificate_root_function) ||
   not
     (aconv candle_real_fixed_proved_certificate_root_lower
        candle_real_jet_certificate_root_lower) ||
   not
     (aconv candle_real_fixed_proved_certificate_root_upper
        candle_real_jet_certificate_root_upper) ||
   not
     (aconv (concl candle_real_fixed_proved_certificate_root_theorem)
        (concl candle_real_jet_certificate_root_theorem)) then
  failwith "fixed proved certificate root theorem drift";;

let _ =
  print_endline
    ("CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_CERTIFICATE_RESULT " ^
     "leaves=16 glues=15 theorem_md5=" ^
     Digest.to_hex
       (Digest.string
         (string_of_thm
           candle_real_fixed_proved_certificate_root_theorem)));;

let _ =
  print_endline "CANDLE_CV_REAL_FLYSPECK_FIXED_PROVED_CERTIFICATE_OK";;

end;;
