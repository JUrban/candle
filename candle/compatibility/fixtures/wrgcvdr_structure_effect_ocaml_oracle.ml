let original_trace = ref [];;
let original_register name precedence associativity =
  original_trace := (name,precedence,associativity)::!original_trace;;

module Original = struct
  let hypermap = true;;
  original_register "has_orders" 12 "right";;
  original_register "cyclic_on" 13 "right";;
end;;

let normalized_trace = ref [];;
let normalized_register name precedence associativity =
  normalized_trace := (name,precedence,associativity)::!normalized_trace;;

module Normalized = struct
  let hypermap = true;;
  let _ = normalized_register "has_orders" 12 "right";;
  let _ = normalized_register "cyclic_on" 13 "right";;
end;;

let original_value_trace = ref [];;
let original_value_effect () =
  original_value_trace := "proof" :: !original_value_trace;
  true;;

module Original_value = struct
  let before = true;;
  original_value_effect ();;
  let after = true;;
end;;

let normalized_value_trace = ref [];;
let normalized_value_effect () =
  normalized_value_trace := "proof" :: !normalized_value_trace;
  true;;

module Normalized_value = struct
  let before = true;;
  let _ = normalized_value_effect ();;
  let after = true;;
end;;

let () =
  if !original_trace = !normalized_trace &&
     !normalized_trace =
       [("cyclic_on",13,"right");("has_orders",12,"right")] &&
     Original.hypermap = Normalized.hypermap &&
     !original_value_trace = !normalized_value_trace &&
     !normalized_value_trace = ["proof"] &&
     Original_value.before = Normalized_value.before &&
     Original_value.after = Normalized_value.after then
    print_endline "WRGCVDR_STRUCTURE_EFFECT_OCAML_ORACLE_OK"
  else failwith "WRGCVDR structure-effect oracle mismatch";;
