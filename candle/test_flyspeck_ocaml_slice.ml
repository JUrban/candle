#use "candle/build/insulate.ml";;
#use "candle/nums.ml";;
#use "candle/pretty.ml";;
#use "candle/ocaml.ml";;

let require condition message = if condition then () else failwith message;;

let assertion_is_distinct =
  try raise (Assert_failure ("fixture", 1, 0)); false
  with Assert_failure _ -> true | Failure _ -> false;;
require assertion_is_distinct "assert compatibility exception mismatch";;

let encoded = Bytes.create 2;;
Bytes.set encoded 0 'A';;
Bytes.set encoded 1 'z';;
require (Bytes.to_string encoded = "Az") "Bytes.set character mismatch";;

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

let two_to_53 = power_num (num_of_int 2) (num_of_int 53);;
let halfway_odd = two_to_53 +/ num_of_int 1;;
require
  (same_float_bits (float_of_num halfway_odd)
     (Float.of_string "9007199254740992"))
  "float_of_num nearest-even integer mismatch";;

let huge_denominator = Num.num_of_string
  "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";;
let huge_near_one =
  (huge_denominator +/ num_of_int 1) // huge_denominator;;
require
  (same_float_bits (float_of_num huge_near_one) Float.one)
  "float_of_num large rational mismatch";;

let two_to_1074 = power_num (num_of_int 2) (num_of_int 1074);;
let minimum_subnormal_num = (num_of_int 1) // two_to_1074;;
require
  (same_float_bits (float_of_num minimum_subnormal_num) minimum_subnormal)
  "float_of_num minimum subnormal mismatch";;
let two_to_1075 = two_to_1074 */ num_of_int 2;;
let halfway_to_zero = (num_of_int 1) // two_to_1075;;
require
  (same_float_bits (float_of_num halfway_to_zero) Float.zero)
  "float_of_num subnormal nearest-even mismatch";;

let eight_from_ldexp = ldexp half 4;;
require (same_float_bits eight_from_ldexp eight) "ldexp normal mismatch";;
require
  (same_float_bits (ldexp Float.one (~-1074)) minimum_subnormal)
  "ldexp normal-to-subnormal mismatch";;
require
  (same_float_bits (ldexp Float.one (~-1075)) Float.zero)
  "ldexp subnormal nearest-even mismatch";;
require
  (same_float_bits (ldexp minimum_subnormal 1074) Float.one)
  "ldexp subnormal-to-normal mismatch";;
require (same_float_bits (ceil (Float.of_string "1.25"))
                          (Float.of_string "2.0"))
  "ceil positive mismatch";;
require (same_float_bits (ceil (Float.of_string "-1.25"))
                          (Float.of_string "-1.0"))
  "ceil negative mismatch";;

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
