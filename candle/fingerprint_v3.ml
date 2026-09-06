(* Candidate structural V3 theorem and kernel-state identities.  This file is
   diagnostic-only until fresh reference sweeps and independent approval;
   fingerprint.ml remains the V2 authority path.  The serializer deliberately
   does not use the HOL pretty-printer: notation, margins and interface
   priorities are mutable.  The full post-load state record covers the
   primitive type and term-constant tables, primitive definitions and global
   axioms. *)

let candle_s1_field s = string_of_int (String.length s) ^ ":" ^ s;;

let candle_s1_hex_digits = "0123456789abcdef";;

(* Build the wire encoding in place.  Expanding a large kernel-state string to
   a character list and then using non-tail-recursive List.map exhausts the
   OCaml stack on real Great 100 states. *)
let candle_s1_hex s =
  let input_length = String.length s in
  if input_length > max_int / 2 then
    failwith "candle_s1_hex: input too large"
  else
    let encoded = Bytes.create (2 * input_length) in
    let rec encode index =
      if index = input_length then () else
      let byte = Char.code (String.get s index) in
      Bytes.set encoded (2 * index)
        (String.get candle_s1_hex_digits (byte / 16));
      Bytes.set encoded (2 * index + 1)
        (String.get candle_s1_hex_digits (byte mod 16));
      encode (index + 1) in
    encode 0;
    Bytes.to_string encoded;;

let candle_s1_node tag fields =
  candle_s1_field tag ^
  candle_s1_field (string_of_int (List.length fields)) ^
  String.concat "" (List.map candle_s1_field fields);;

(* HOL Light deliberately invents numeric names for some schematic type
   variables, free variables and anonymous specification constants.  Their
   numeric suffixes depend on the evaluator's allocation schedule and are not
   part of the logical object.  Rank those names by their monotone numeric
   suffix before serialization while retaining all ordinary user names. *)
let rec candle_s1_decimal_from value index =
  if index = String.length value then true else
  let character = String.get value index in
  Char.code '0' <= Char.code character &&
  Char.code character <= Char.code '9' &&
  candle_s1_decimal_from value (index + 1);;

let candle_s1_generated_name prefix value =
  let prefix_length = String.length prefix in
  String.length value > prefix_length &&
  String.sub value 0 prefix_length = prefix &&
  candle_s1_decimal_from value prefix_length &&
  int_of_string
    (String.sub value prefix_length (String.length value - prefix_length)) > 0;;

let candle_s1_generated_number prefix value =
  let prefix_length = String.length prefix in
  int_of_string
    (String.sub value prefix_length (String.length value - prefix_length));;

let candle_s1_reserved_name prefix value =
  let prefix_length = String.length prefix in
  String.length value > prefix_length &&
  String.sub value 0 prefix_length = prefix &&
  candle_s1_decimal_from value prefix_length;;

let candle_s1_sort_generated prefix values =
  let ordered = List.sort
    (fun left right ->
      Int.compare (candle_s1_generated_number prefix left)
                  (candle_s1_generated_number prefix right)) values in
  let rec unique = function
      first :: (second :: _ as rest) ->
        if first = second then unique rest else first :: unique rest
    | values -> values in
  unique ordered;;

let rec candle_s1_generated_rank value index = function
    [] -> failwith "candle_s1_generated_rank"
  | head :: rest ->
      if value = head then index
      else candle_s1_generated_rank value (index + 1) rest;;

let candle_s1_canonical_generated prefix replacement values value =
  if candle_s1_generated_name prefix value then
    replacement ^
    string_of_int (candle_s1_generated_rank value 0 values)
  else if candle_s1_reserved_name replacement value then
    failwith "candle_s1_canonical_generated: reserved name"
  else value;;

let rec candle_s1_type_generated_names ty =
  if is_vartype ty then
    let name = dest_vartype ty in
    if candle_s1_generated_name "?" name then [name] else []
  else
    let _,arguments = dest_type ty in
    List.concat (List.map candle_s1_type_generated_names arguments);;

let candle_s1_type_names types =
  candle_s1_sort_generated "?"
    (List.concat (List.map candle_s1_type_generated_names types));;

let rec candle_s1_type_with_names generated_types ty =
  if is_vartype ty then
    candle_s1_node "type-variable"
      [candle_s1_canonical_generated "?" "?CANDLE_GENERATED_TYPE_"
         generated_types (dest_vartype ty)]
  else
    let name,args = dest_type ty in
    candle_s1_node "type-application"
      [name;
       candle_s1_list
         (List.map (candle_s1_type_with_names generated_types) args)]

and candle_s1_list items = candle_s1_node "list" items;;

let candle_s1_type ty =
  candle_s1_type_with_names
    (candle_s1_type_names [ty]) ty;;

let rec candle_s1_bound_index n variable = function
    [] -> None
  | head::tail ->
      if variable = head then Some n
      else candle_s1_bound_index (n + 1) variable tail;;

let rec candle_s1_term_generated_type_names term =
  let own = candle_s1_type_generated_names (type_of term) in
  if is_comb term then
    let operator,operand = dest_comb term in
    own @ candle_s1_term_generated_type_names operator @
          candle_s1_term_generated_type_names operand
  else if is_abs term then
    let variable,body = dest_abs term in
    own @ candle_s1_term_generated_type_names variable @
          candle_s1_term_generated_type_names body
  else own;;

let rec candle_s1_term_generated_free_names environment term =
  if is_var term then
    (match candle_s1_bound_index 0 term environment with
       Some _ -> []
     | None ->
         let name,_ = dest_var term in
         if candle_s1_generated_name "_" name then [name] else [])
  else if is_comb term then
    let operator,operand = dest_comb term in
    candle_s1_term_generated_free_names environment operator @
    candle_s1_term_generated_free_names environment operand
  else if is_abs term then
    let variable,body = dest_abs term in
    candle_s1_term_generated_free_names (variable::environment) body
  else [];;

let candle_s1_term_names terms =
  let generated_types = candle_s1_sort_generated "?"
    (List.concat (List.map candle_s1_term_generated_type_names terms))
  and generated_variables = candle_s1_sort_generated "_"
    (List.concat
      (List.map (candle_s1_term_generated_free_names []) terms)) in
  generated_types,generated_variables;;

let candle_s1_generated_constant_names () =
  candle_s1_sort_generated "_"
    (List.filter (candle_s1_generated_name "_")
      (List.map fst (constants())));;

let rec candle_s1_term_with_names generated_types generated_variables
                                      generated_constants environment term =
  if is_var term then
    let name,ty = dest_var term in
    (match candle_s1_bound_index 0 term environment with
       None -> candle_s1_node "free-variable"
         [candle_s1_canonical_generated "_" "_CANDLE_GENERATED_VARIABLE_"
            generated_variables name;
          candle_s1_type_with_names generated_types ty]
     | Some index ->
         candle_s1_node "bound-variable"
           [string_of_int index;
            candle_s1_type_with_names generated_types ty])
  else if is_const term then
    let name,ty = dest_const term in
    candle_s1_node "constant"
      [candle_s1_canonical_generated "_" "_CANDLE_GENERATED_CONSTANT_"
         generated_constants name;
       candle_s1_type_with_names generated_types ty]
  else if is_comb term then
    let operator,operand = dest_comb term in
    candle_s1_node "combination"
      [candle_s1_term_with_names generated_types generated_variables
         generated_constants environment operator;
       candle_s1_term_with_names generated_types generated_variables
         generated_constants environment operand]
  else if is_abs term then
    let variable,body = dest_abs term in
    candle_s1_node "abstraction"
      [candle_s1_type_with_names generated_types (type_of variable);
       candle_s1_term_with_names generated_types generated_variables
         generated_constants (variable::environment) body]
  else failwith "candle_s1_term: unknown term form";;

let candle_s1_term environment term =
  let generated_types,generated_variables = candle_s1_term_names [term] in
  candle_s1_term_with_names generated_types generated_variables
    (candle_s1_generated_constant_names ()) environment term;;

let candle_s1_closed_term term = candle_s1_term [] term;;

let candle_s1_sorted_terms terms =
  List.sort String.compare (List.map candle_s1_closed_term terms);;

let candle_s1_theorem_parts_with_constants generated_constants theorem =
  let terms = concl theorem :: hyp theorem in
  let generated_types,generated_variables = candle_s1_term_names terms in
  let serialize = candle_s1_term_with_names
    generated_types generated_variables generated_constants [] in
  let hypotheses = candle_s1_list
    (List.sort String.compare (List.map serialize (hyp theorem)))
  and conclusion = serialize (concl theorem) in
  candle_s1_node "theorem" [hypotheses; conclusion],hypotheses,conclusion;;

let candle_s1_theorem_parts theorem =
  candle_s1_theorem_parts_with_constants
    (candle_s1_generated_constant_names ()) theorem;;

let candle_s1_global_axioms () =
  let generated_constants = candle_s1_generated_constant_names () in
  let serialized =
    List.map (fun theorem ->
      let identity,_,_ =
        candle_s1_theorem_parts_with_constants generated_constants theorem in
      identity)
      (axioms()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_type_constants () =
  let serialized =
    List.map (fun (name,arity) ->
      candle_s1_node "type-constant-declaration"
        [name; string_of_int arity]) (types()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_term_constants () =
  let generated_constants = candle_s1_generated_constant_names () in
  let serialized =
    List.map (fun (name,ty) ->
      candle_s1_node "term-constant-declaration"
        [candle_s1_canonical_generated "_" "_CANDLE_GENERATED_CONSTANT_"
           generated_constants name;
         candle_s1_type ty]) (constants()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_definitions () =
  let generated_constants = candle_s1_generated_constant_names () in
  let serialized =
    List.map (fun theorem ->
      let identity,_,_ =
        candle_s1_theorem_parts_with_constants generated_constants theorem in
      identity)
      (definitions()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_kernel_state_parts () =
  let type_constants = candle_s1_type_constants ()
  and term_constants = candle_s1_term_constants ()
  and primitive_definitions = candle_s1_definitions ()
  and global_axioms = candle_s1_global_axioms () in
  let state = candle_s1_node "kernel-state"
    [type_constants; term_constants; primitive_definitions; global_axioms] in
  state,type_constants,term_constants,primitive_definitions,global_axioms;;

let candle_s1_emit_fingerprint name theorem =
  let theorem_identity,hypothesis_identity,conclusion_identity =
    candle_s1_theorem_parts theorem in
  let axiom_identity = candle_s1_global_axioms () in
  print_endline
    ("CANDLE_FINGERPRINT_V3\t" ^ candle_s1_hex name ^ "\t" ^
     candle_s1_hex theorem_identity ^ "\t" ^
     candle_s1_hex hypothesis_identity ^ "\t" ^
     candle_s1_hex conclusion_identity ^ "\t" ^
     candle_s1_hex axiom_identity ^ "\t" ^
     string_of_int (List.length (hyp theorem)) ^ "\t" ^
     string_of_int (List.length (axioms())));;

let candle_s1_emit_state_fingerprint () =
  let state,type_constants,term_constants,primitive_definitions,global_axioms =
    candle_s1_kernel_state_parts () in
  print_endline
    ("CANDLE_STATE_FINGERPRINT_V3\t" ^
     candle_s1_hex state ^ "\t" ^
     candle_s1_hex type_constants ^ "\t" ^
     candle_s1_hex term_constants ^ "\t" ^
     candle_s1_hex primitive_definitions ^ "\t" ^
     candle_s1_hex global_axioms ^ "\t" ^
     string_of_int (List.length (types())) ^ "\t" ^
     string_of_int (List.length (constants())) ^ "\t" ^
     string_of_int (List.length (definitions())) ^ "\t" ^
     string_of_int (List.length (axioms())));;
