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

let () =
  if !original_trace = !normalized_trace &&
     !normalized_trace =
       [("cyclic_on",13,"right");("has_orders",12,"right")] &&
     Original.hypermap = Normalized.hypermap then
    print_endline "WRGCVDR_STRUCTURE_EFFECT_OCAML_ORACLE_OK"
  else failwith "WRGCVDR structure-effect oracle mismatch";;
