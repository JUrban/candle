(* Focused checks for the canonical V3 fingerprint name policy.  Load this
   after hol.ml and candle/fingerprint_v3.ml; it intentionally creates terms
   only and does not extend the kernel state. *)

let candle_v3_check label condition =
  if condition then () else failwith ("fingerprint V3 test: " ^ label);;

let candle_v3_reserved_rejected prefix replacement value =
  try
    let _ = candle_s1_canonical_generated prefix replacement [] value in
    false
  with Failure _ -> true;;

candle_v3_check "positive generated type name"
  (candle_s1_generated_name "?" "?1");;
candle_v3_check "zero is not a generated type name"
  (not (candle_s1_generated_name "?" "?0"));;
candle_v3_check "nonnumeric type name is not generated"
  (not (candle_s1_generated_name "?" "?ordinary"));;
candle_v3_check "generated names sort numerically and uniquely"
  (candle_s1_sort_generated "_" ["_20"; "_7"; "_20"] =
   ["_7"; "_20"]);;

candle_v3_check "reserved type name is rejected"
  (candle_v3_reserved_rejected "?" "?CANDLE_GENERATED_TYPE_"
    "?CANDLE_GENERATED_TYPE_0");;
candle_v3_check "reserved free-variable name is rejected"
  (candle_v3_reserved_rejected "_" "_CANDLE_GENERATED_VARIABLE_"
    "_CANDLE_GENERATED_VARIABLE_0");;
candle_v3_check "reserved constant name is rejected"
  (candle_v3_reserved_rejected "_" "_CANDLE_GENERATED_CONSTANT_"
    "_CANDLE_GENERATED_CONSTANT_0");;

let candle_v3_test_bool = mk_type("bool",[]);;
let candle_v3_bound = mk_var("_7",candle_v3_test_bool);;
candle_v3_check "numeric bound variable is not collected as free"
  (candle_s1_term_generated_free_names []
    (mk_abs(candle_v3_bound,candle_v3_bound)) = []);;
candle_v3_check "numeric free variable is collected"
  (candle_s1_term_generated_free_names [] candle_v3_bound = ["_7"]);;

let candle_v3_free_left = mk_var("_17",candle_v3_test_bool)
and candle_v3_free_right = mk_var("_901",candle_v3_test_bool);;
candle_v3_check "generated free-variable alpha normalization"
  (candle_s1_theorem_parts (ASSUME candle_v3_free_left) =
   candle_s1_theorem_parts (ASSUME candle_v3_free_right));;

let candle_v3_named_left = mk_var("left",candle_v3_test_bool)
and candle_v3_named_right = mk_var("right",candle_v3_test_bool);;
candle_v3_check "ordinary free-variable names remain significant"
  (candle_s1_theorem_parts (ASSUME candle_v3_named_left) <>
   candle_s1_theorem_parts (ASSUME candle_v3_named_right));;

let candle_v3_type_left =
  mk_type("fun",[mk_vartype "?17"; mk_vartype "?20"])
and candle_v3_type_right =
  mk_type("fun",[mk_vartype "?901"; mk_vartype "?990"])
and candle_v3_type_swapped =
  mk_type("fun",[mk_vartype "?990"; mk_vartype "?901"]);;
candle_v3_check "generated type-variable alpha normalization"
  (candle_s1_type candle_v3_type_left =
   candle_s1_type candle_v3_type_right);;
candle_v3_check "generated type-variable structure remains significant"
  (candle_s1_type candle_v3_type_left <>
   candle_s1_type candle_v3_type_swapped);;
candle_v3_check "ordinary type-variable names remain significant"
  (candle_s1_type (mk_vartype "A") <>
   candle_s1_type (mk_vartype "B"));;

print_endline "CANDLE_CANONICAL_V3_FOCUSED_TESTS_OK";;
