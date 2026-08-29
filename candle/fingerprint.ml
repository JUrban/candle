(* Structural S1 theorem and kernel-state identities. This deliberately does
   not use the HOL pretty-printer: notation, margins and interface priorities
   are mutable.  The full post-load state record covers the primitive type and
   term-constant tables, primitive definitions and global axioms. *)

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
    for index = 0 to input_length - 1 do
      let byte = Char.code (String.get s index) in
      Bytes.set encoded (2 * index)
        (String.get candle_s1_hex_digits (byte / 16));
      Bytes.set encoded (2 * index + 1)
        (String.get candle_s1_hex_digits (byte mod 16))
    done;
    Bytes.to_string encoded;;

let candle_s1_node tag fields =
  candle_s1_field tag ^
  candle_s1_field (string_of_int (List.length fields)) ^
  String.concat "" (List.map candle_s1_field fields);;

let rec candle_s1_type ty =
  if is_vartype ty then
    candle_s1_node "type-variable" [dest_vartype ty]
  else
    let name,args = dest_type ty in
    candle_s1_node "type-application"
      [name; candle_s1_list (List.map candle_s1_type args)]

and candle_s1_list items = candle_s1_node "list" items;;

let rec candle_s1_bound_index n variable = function
    [] -> None
  | head::tail ->
      if variable = head then Some n
      else candle_s1_bound_index (n + 1) variable tail;;

let rec candle_s1_term environment term =
  if is_var term then
    let name,ty = dest_var term in
    (match candle_s1_bound_index 0 term environment with
       None -> candle_s1_node "free-variable" [name; candle_s1_type ty]
     | Some index ->
         candle_s1_node "bound-variable"
           [string_of_int index; candle_s1_type ty])
  else if is_const term then
    let name,ty = dest_const term in
    candle_s1_node "constant" [name; candle_s1_type ty]
  else if is_comb term then
    let operator,operand = dest_comb term in
    candle_s1_node "combination"
      [candle_s1_term environment operator;
       candle_s1_term environment operand]
  else if is_abs term then
    let variable,body = dest_abs term in
    candle_s1_node "abstraction"
      [candle_s1_type (type_of variable);
       candle_s1_term (variable::environment) body]
  else failwith "candle_s1_term: unknown term form";;

let candle_s1_closed_term term = candle_s1_term [] term;;

let candle_s1_sorted_terms terms =
  List.sort String.compare (List.map candle_s1_closed_term terms);;

let candle_s1_theorem_parts theorem =
  let hypotheses = candle_s1_list (candle_s1_sorted_terms (hyp theorem))
  and conclusion = candle_s1_closed_term (concl theorem) in
  candle_s1_node "theorem" [hypotheses; conclusion],hypotheses,conclusion;;

let candle_s1_global_axioms () =
  let serialized =
    List.map (fun theorem ->
      let identity,_,_ = candle_s1_theorem_parts theorem in identity)
      (axioms()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_type_constants () =
  let serialized =
    List.map (fun (name,arity) ->
      candle_s1_node "type-constant-declaration"
        [name; string_of_int arity]) (types()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_term_constants () =
  let serialized =
    List.map (fun (name,ty) ->
      candle_s1_node "term-constant-declaration"
        [name; candle_s1_type ty]) (constants()) in
  candle_s1_list (List.sort String.compare serialized);;

let candle_s1_definitions () =
  let serialized =
    List.map (fun theorem ->
      let identity,_,_ = candle_s1_theorem_parts theorem in identity)
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
    ("CANDLE_FINGERPRINT_V2\t" ^ candle_s1_hex name ^ "\t" ^
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
    ("CANDLE_STATE_FINGERPRINT_V2\t" ^
     candle_s1_hex state ^ "\t" ^
     candle_s1_hex type_constants ^ "\t" ^
     candle_s1_hex term_constants ^ "\t" ^
     candle_s1_hex primitive_definitions ^ "\t" ^
     candle_s1_hex global_axioms ^ "\t" ^
     string_of_int (List.length (types())) ^ "\t" ^
     string_of_int (List.length (constants())) ^ "\t" ^
     string_of_int (List.length (definitions())) ^ "\t" ^
     string_of_int (List.length (axioms())));;
