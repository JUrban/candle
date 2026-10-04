(* ========================================================================== *)
(* Complete generated adaptive plan for the genuine action-296 right leaf.  *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is compact untrusted plan data.  The     *)
(* reflected checker remains responsible for checking every final cell and  *)
(* every topology operation.  It is the exact 1,061-root plan independently *)
(* replayed in the retained September 28 runs.                               *)
(*                                                                            *)
(* Expanded policy SHA-256:                                                  *)
(*   61233bfa9125f185a5d576176f298ea6111acbdf092f1940b113b26b85b9bac4 *)
(* Compact preorder SHA-256:                                                 *)
(*   d2dc1e54e0923978cca0eff6c53193c42d50b85413d8cebef95705106d5f6b7e *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_action296_forest_plan.ml";;

module Candle_cv_action296_fixed_outer_generated_plan = struct

open Candle_cv_action296_forest_plan;;

(* L is a leaf.  Digits 1--6 are preorder split axes, each followed by its
   left and right subplans.  Semicolons separate the 1,061 original roots. *)
let candle_action296_fixed_outer_compact_plan =
  "4LL;4LL;4LL;4LL;L;L;L;L;L;4LL;L;L;4LL;4LL;L;L;4LL;L;4LL;4LL;2LL;4LL;4LL;4LL;L;L;4LL;L;4LL;L;L;4L" ^
  "L;4LL;4LL;4LL;L;L;L;L;4LL;4LL;4LL;L;L;L;L;L;L;L;4LL;L;4LL;L;L;L;4LL;L;4LL;L;4LL;4LL;4LL;L;4LL;L;" ^
  "L;L;L;4LL;4LL;4LL;L;L;4LL;L;4LL;L;L;L;4LL;L;4LL;4LL;4LL;4LL;L;4LL;4LL;4LL;4LL;4LL;L;L;L;L;L;L;L;" ^
  "4LL;L;4LL;4LL;L;L;L;4LL;L;4LL;L;L;L;4LL;L;L;L;4LL;L;L;4LL;4LL;L;L;4LL;L;4LL;4LL;4LL;4LL;L;L;L;L;" ^
  "L;4LL;4LL;L;L;4LL;4LL;4LL;4LL;L;L;L;4LL;L;L;L;4LL;L;L;L;4LL;4LL;4LL;4LL;4LL;L;L;4LL;L;4LL;L;L;4L" ^
  "L;L;L;4LL;4LL;L;4LL;4LL;4LL;L;4LL;L;L;L;L;L;4LL;4LL;L;L;4LL;4LL;4LL;L;L;L;4LL;4LL;4LL;4LL;4LL;4L" ^
  "L;L;4LL;4LL;L;L;L;L;4LL;L;L;L;L;4LL;4LL;4LL;L;L;4LL;4LL;4LL;4LL;4LL;4LL;L;L;L;4LL;L;L;4LL;4LL;4L" ^
  "L;L;4LL;L;L;L;L;L;L;L;L;L;4LL;L;L;4LL;4LL;L;L;4LL;4LL;L;L;L;4LL;L;L;L;4LL;L;4LL;4LL;L;L;L;L;L;1L" ^
  "L;L;L;L;L;L;L;L;L;L;L;4LL;L;L;4LL;4LL;4LL;L;L;L;L;L;L;4LL;L;4LL;4LL;L;L;L;L;L;L;L;L;L;L;L;L;4LL;" ^
  "L;L;L;2LL;4LL;4LL;4LL;L;L;4LL;L;4LL;L;L;L;L;L;L;L;L;L;L;4LL;L;L;L;L;4LL;L;L;4LL;4LL;4LL;4LL;L;4L" ^
  "L;4LL;2LL;2LL;4LL;4LL;L;1LL;4LL;4LL;4LL;L;L;L;4LL;L;L;4LL;L;L;4LL;L;L;4LL;4LL;4LL;4LL;4LL;4LL;4L" ^
  "L;L;L;4LL;4LL;L;4LL;L;L;1LL;4LL;L;4LL;4LL;1LL;4LL;L;L;L;4LL;L;L;L;4LL;4LL;L;4LL;4LL;L;L;L;4LL;4L" ^
  "L;L;4LL;L;L;L;L;4LL;L;4LL;L;4LL;L;L;L;L;L;L;L;4LL;4LL;4LL;L;L;L;4LL;L;L;L;L;4LL;4LL;4LL;L;4LL;L;" ^
  "4LL;4LL;L;L;L;L;4LL;L;4LL;L;L;L;4LL;4LL;L;4LL;4LL;L;L;4LL;L;L;L;L;4LL;L;L;L;4LL;L;L;1LL;4LL;L;2L" ^
  "L;4LL;L;2LL;4LL;1LL;4LL;4LL;L;L;4LL;L;4LL;L;L;L;L;L;L;L;L;4LL;L;4LL;L;L;L;4LL;L;2LL;4LL;4LL;L;L;" ^
  "L;L;L;L;L;4LL;L;4LL;4LL;L;L;L;L;L;L;L;L;L;L;L;L;4LL;L;L;4LL;4LL;L;L;4LL;4LL;L;L;4LL;L;L;L;4LL;4L" ^
  "L;L;L;L;L;L;L;L;4LL;L;L;L;L;4LL;L;L;L;4LL;L;L;L;4LL;L;L;L;L;4LL;4LL;4LL;4LL;4LL;4LL;4LL;4LL;L;L;" ^
  "4LL;L;L;L;L;4LL;1LL;4LL;L;1LL;4LL;4LL;4LL;4LL;4LL;L;L;4LL;L;4LL;L;L;4LL;L;L;4LL;4LL;L;L;L;L;L;L;" ^
  "4LL;L;4LL;L;4LL;L;4LL;L;4LL;L;L;L;4LL;L;L;4LL;4LL;L;L;4LL;4LL;L;L;L;4LL;L;L;4LL;L;4LL;4LL;L;4LL;" ^
  "L;L;4LL;L;L;L;4LL;4LL;4LL;L;4LL;L;64LLL;1LL;4LL;4LL;L;4LL;4LL;64LLL;1LL;4LL;4LL;L;4LL;L;4LL;L;4L" ^
  "L;L;L;L;L;L;6LL;4LL;L;64LLL;4LL;L;64LLL;4LL;4LL;64LLL;4LL;L;6LL;4LL;L;4LL;L;4LL;L;64LLL;L;L;6LL;" ^
  "6LL;1LL;4LL;4LL;4LL;4LL;4LL;4LL;L;L;4LL;L;L;L;L;L;1LL;4LL;L;4LL;4LL;L;4LL;4LL;L;4LL;L;4LL;L;4LL;" ^
  "L;L;L;1LL;L;L;4LL;4LL;L;L;4LL;4LL;4LL;L;4LL;L;L;L;4LL;L;1LL;L;L;L;L;L;L;4LL;L;L;1LL;1LL;4LL;L;L;" ^
  "L;L;L;L;4LL;L;L;1LL;1LL;4LL;L;L;4LL;L;L;L;4LL;L;L;L;L;4LL;4LL;L;L;L;L;4LL;L;4LL;L;L;4LL;L;L;4LL;" ^
  "L;L;4LL;4LL;4LL;4LL;4LL;4LL;L;4LL;4LL;4LL;4LL;L;L;4LL;L;L;4LL;L;4LL;4LL;L;4LL;L;4LL;L;L;4LL;L;4L" ^
  "L;4LL;L;L;L;L;L;L;L;L;4LL;L;4LL;L;4LL;L;4LL;L;1LL;L;L;L;L;L;L;1LL;4LL;L;L;L;L;4LL;L;L;L;L;L;4LL;" ^
  "L;L;L;L;L;L;L;L;L;L;L;4LL;4LL;1LL;L;L;4LL;L;4LL;L;4LL;L;4LL;4LL;4LL;L;L;4LL;L;4LL;4LL;1LL;1LL;4L" ^
  "L;L;4LL;4LL;14LLL;1LL;L;L;L;L;4LL;4LL;1LL;4LL;4LL;L;L;4LL;4LL;4LL;L;L;4LL;4LL;L;4LL;L;L;1LL;L;L;" ^
  "4LL;L;L;4LL;L;L;L;L;4LL;L;L;4LL;L;L;4LL;4LL;L;4LL;L;L;L;L;L;L;L;L;L;4LL;1LL;L;4LL;L;L;4LL;L;L;L;" ^
  "L;4LL;L;L;L;L;L;L;L;L;L;L;L;4LL;L;L;4LL;1LL;4LL;L;L;L;1LL;4LL;1LL;L;4LL;L;4LL;L;4LL;L;4LL;L;4LL;" ^
  "4LL;4LL;L;L;4LL;4LL;L;4LL;1LL;L;L;L;L;4LL;L;4LL;L;4LL;L;14LLL;L;L;1LL;4LL;L;1LL;L;L;1LL;4LL;L;L;" ^
  "L;L;L;1LL;6LL;1LL;1LL;4LL;41LL1LL;1LL;1LL;1LL;41LL1LL;1LL;1LL;4LL;14LLL;1LL;1LL;1LL;1LL;4LL;4LL;" ^
  "4LL";;

let candle_action296_fixed_outer_axis = function
  | '1' -> 1 | '2' -> 2 | '3' -> 3
  | '4' -> 4 | '5' -> 5 | '6' -> 6
  | _ -> failwith "action296 compact plan: invalid split axis";;

let rec candle_action296_fixed_outer_decode data offset =
  if offset >= String.length data then
    failwith "action296 compact plan: truncated root";
  let symbol = String.get data offset in
  if symbol = 'L' then
    Candle_action296_forest_leaf,offset + 1,1
  else
    let axis = candle_action296_fixed_outer_axis symbol in
    let left,after_left,left_cells =
      candle_action296_fixed_outer_decode data (offset + 1) in
    let right,after_right,right_cells =
      candle_action296_fixed_outer_decode data after_left in
    Candle_action296_forest_split (axis,left,right),after_right,
    left_cells + right_cells;;

let rec candle_action296_fixed_outer_decode_roots
    data expected offset reversed cells =
  let plan,next,root_cells =
    candle_action296_fixed_outer_decode data offset in
  let reversed' = (expected,plan) :: reversed in
  let cells' = cells + root_cells in
  if expected = 1060 then begin
    if next <> String.length data then
      failwith "action296 compact plan: trailing data";
    List.rev reversed',cells'
  end else begin
    if next >= String.length data || String.get data next <> ';' then
      failwith "action296 compact plan: missing root separator";
    candle_action296_fixed_outer_decode_roots
      data (expected + 1) (next + 1) reversed' cells'
  end;;

let candle_action296_fixed_outer_generated_roots,
    candle_action296_fixed_outer_generated_final_cells =
  candle_action296_fixed_outer_decode_roots
    candle_action296_fixed_outer_compact_plan 0 0 [] 0;;

let candle_action296_fixed_outer_expected_forest_digest =
  "638431efbc713f147bd8c855f79f72ec";;

if length candle_action296_fixed_outer_generated_roots <> 1061 ||
   candle_action296_fixed_outer_generated_final_cells <> 1538 then
  failwith "action296 compact plan: complete shape drift";;

print_endline
  "CANDLE_CV_ACTION296_FIXED_OUTER_GENERATED_PLAN_OK DEVELOPMENT_NON_RELEASE roots=1061 cells=1538";;

end;;
