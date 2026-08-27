(* Structural S1 theorem identities. This deliberately does not use the HOL
   pretty-printer: notation, margins and interface priorities are mutable. *)

let candle_s1_field s = string_of_int (String.length s) ^ ":" ^ s;;

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

let candle_s1_emit_fingerprint name theorem =
  let theorem_identity,hypothesis_identity,conclusion_identity =
    candle_s1_theorem_parts theorem in
  let axiom_identity = candle_s1_global_axioms () in
  print_endline
    ("CANDLE_FINGERPRINT_V1\t" ^ String.escaped name ^ "\t" ^
     String.escaped theorem_identity ^ "\t" ^
     String.escaped hypothesis_identity ^ "\t" ^
     String.escaped conclusion_identity ^ "\t" ^
     String.escaped axiom_identity ^ "\t" ^
     string_of_int (List.length (hyp theorem)) ^ "\t" ^
     string_of_int (List.length (axioms())));;
