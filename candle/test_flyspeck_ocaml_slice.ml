#use "candle/build/insulate.ml";;
#use "candle/nums.ml";;
#use "candle/pretty.ml";;
#use "candle/ocaml.ml";;

let require condition message = if condition then () else failwith message;;

let same_float_bits left right =
  Cake.Double.sign left = Cake.Double.sign right &&
  Cake.Double.exponent left = Cake.Double.exponent right &&
  Cake.Double.significand left = Cake.Double.significand right;;

let half = Float.of_string "0.5";;
let eight = Float.of_string "8.0";;
let eight_fraction, eight_exponent = frexp eight;;
require (same_float_bits eight_fraction half && eight_exponent = 4)
  "frexp normal mismatch";;

let negative_zero =
  Cake.Double.construct (Cake.Word64.fromInt 1) (Cake.Word64.fromInt 0)
    (Cake.Word64.fromInt 0);;
let zero_fraction, zero_exponent = frexp negative_zero;;
require (same_float_bits zero_fraction negative_zero && zero_exponent = 0)
  "frexp signed-zero mismatch";;

let minimum_subnormal =
  Cake.Double.construct (Cake.Word64.fromInt 0) (Cake.Word64.fromInt 0)
    (Cake.Word64.fromInt 1);;
let subnormal_fraction, subnormal_exponent = frexp minimum_subnormal;;
require
  (same_float_bits subnormal_fraction half && subnormal_exponent = ~-1073)
  "frexp subnormal mismatch";;

let infinity_fraction, infinity_exponent = frexp Cake.Double.posinf64;;
require
  (same_float_bits infinity_fraction Cake.Double.posinf64 && infinity_exponent = 0)
  "frexp infinity mismatch";;

let three_quarters = (num_of_int 3) // (num_of_int 4);;
require
  (same_float_bits (float_of_num three_quarters) (Float.of_string "0.75"))
  "float_of_num rational mismatch";;

let linear = ((Hashtbl.create 3) : (string, int) Hashtbl.t);;
Hashtbl.add linear "k" 1;;
Hashtbl.add linear "k" 2;;
require (Hashtbl.find linear "k" = 2 && Hashtbl.length linear = 2)
  "Hashtbl.add binding-stack mismatch";;
Hashtbl.remove linear "k";;
require (Hashtbl.find linear "k" = 1 && Hashtbl.length linear = 1)
  "Hashtbl.remove binding-stack mismatch";;
Hashtbl.replace linear "k" 7;;
require (Hashtbl.find linear "k" = 7 && Hashtbl.mem linear "k")
  "Hashtbl.replace mismatch";;
Hashtbl.clear linear;;
require (Hashtbl.length linear = 0 && not (Hashtbl.mem linear "k"))
  "Hashtbl.clear mismatch";;

let ordered =
  ((Hashtbl.create_ordered 3 String.hash String.compare) :
    (string, int) Hashtbl.t);;
Hashtbl.add ordered "b" 2;;
Hashtbl.add ordered "a" 1;;
require (Hashtbl.find ordered "a" = 1 && Hashtbl.length ordered = 2)
  "ordered Hashtbl mismatch";;

let initialized = Array.init 4 (fun index -> index * index);;
require (Array.length initialized = 4 && Array.get initialized 3 = 9)
  "Array.init mismatch";;
require (Sys.word_size = 64) "Sys.word_size mismatch";;
Gc.compact ();;

require (Stdlib.compare "same" "same" = 0)
  "Stdlib.compare equality mismatch";;
let compare_rejected =
  try let _ = Stdlib.compare "left" "right" in false with Failure _ -> true;;
require compare_rejected "Stdlib.compare must fail closed without ordering";;
let hash_rejected =
  try let _ = Hashtbl.hash "key" in false with Failure _ -> true;;
require hash_rejected "Hashtbl.hash must fail closed";;

print_endline "CANDLE_FLYSPECK_OCAML_SLICE_OK";;
