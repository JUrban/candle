let prove_by_refinement _ = "strictbuild";;

module Candle_marchal3_prove_by_refinement = struct
  let prove_by_refinement _ = "strictbuild";;
end;;

module Candle_marchal3_refinement = struct
  let prove_by_refinement _ = "refinement";;
end;;

module Candle_marchal3_vukhacky_tactics = struct
  open Candle_marchal3_refinement;;
  let vukhacky_value = true;;
end;;

module Candle_marchal3_qzyzmjc = struct
  open Candle_marchal3_vukhacky_tactics;;
  let qzyzmjc_value = true;;
end;;

module Candle_marchal3_support = struct
  open Candle_marchal3_vukhacky_tactics;;
  let support_value = true;;
end;;

module Candle_marchal3_normalized = struct
  open Candle_marchal3_qzyzmjc;;
  open Candle_marchal3_support;;
  let prove_by_refinement =
    Candle_marchal3_prove_by_refinement.prove_by_refinement;;
  let selected = prove_by_refinement ();;
end;;

let candle_marchal3_open_resolution_ok =
  Candle_marchal3_normalized.selected = "strictbuild";;
