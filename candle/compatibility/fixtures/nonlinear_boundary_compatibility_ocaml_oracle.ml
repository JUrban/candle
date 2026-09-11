let integers = [min_int;-7;-1;0;1;42;max_int];;
let strings = ["";"plain";"%d";"a b\n\"c\""];;

let all predicate values = List.for_all predicate values;;

let f4_id i3 i4 i5 i6 =
  "ZTGIJCF4 " ^ string_of_int i3 ^ " " ^ string_of_int i4 ^
  " " ^ string_of_int i5 ^ " " ^ string_of_int i6 ^ " 1821661595";;

let simple_formats_ok =
  all
    (fun first ->
      all
        (fun second ->
          Printf.sprintf "ZTGIJCF4 %d %d %d %d 1821661595"
            first second 0 max_int =
              f4_id first second 0 max_int &&
          Printf.sprintf "QITNPEA1 %d %d 9063653052 A" first second =
            "QITNPEA1 " ^ string_of_int first ^ " " ^
              string_of_int second ^ " 9063653052 A" &&
          Printf.sprintf "OXLZLEZ 6346351218 %d %d" first second =
            "OXLZLEZ 6346351218 " ^ string_of_int first ^ " " ^
              string_of_int second &&
          Printf.sprintf "7550003505 %d %d %d" first second min_int =
            "7550003505 " ^ string_of_int first ^ " " ^
              string_of_int second ^ " " ^ string_of_int min_int &&
          Printf.sprintf "prep-%s split(%d/%d)" "S" first second =
            "prep-S split(" ^ string_of_int first ^ "/" ^
              string_of_int second ^ ")")
        integers)
    integers;;

let original_cc name args rhs =
  String.concat "\n"
    [Printf.sprintf "double %s(" name;
     String.concat "," (List.map (fun value -> "double " ^ value) args);
     Printf.sprintf ") { \nreturn ( %s ); \n}\n\n" rhs];;

let replacement_cc name args rhs =
  String.concat "\n"
    ["double " ^ name ^ "(";
     String.concat "," (List.map (fun value -> "double " ^ value) args);
     ") { \nreturn ( " ^ rhs ^ " ); \n}\n\n"];;

let original_case p values index =
  Printf.sprintf "case %d: *ret = (%s) - (%s); break;"
    index (List.nth values index) p;;

let replacement_case p values index =
  "case " ^ string_of_int index ^ ": *ret = (" ^
  List.nth values index ^ ") - (" ^ p ^ "); break;";;

let original_vardecl y name index =
  Printf.sprintf "double %s = %s[%d];" name y index;;

let replacement_vardecl y name index =
  "double " ^ name ^ " = " ^ y ^ "[" ^ string_of_int index ^ "];";;

let original_glpk count id dart form =
  Printf.sprintf
    "ineq%d 'ID[%s]' \n  { (i,j) in %s } : \n  %s >= 0.0;\n\n"
    count id dart form;;

let replacement_glpk count id dart form =
  "ineq" ^ string_of_int count ^ " 'ID[" ^ id ^
  "]' \n  { (i,j) in " ^ dart ^ " } : \n  " ^ form ^
  " >= 0.0;\n\n";;

let original_domain fs variables body result remaining =
  Printf.sprintf
    " %s %s = \n  let _ = ( %s ) || failwith \"domain6:%s\" in \n      ( %s ) %s"
    fs variables body fs result remaining;;

let replacement_domain fs variables body result remaining =
  " " ^ fs ^ " " ^ variables ^
  " = \n  let _ = ( " ^ body ^ " ) || failwith \"domain6:" ^ fs ^
  "\" in \n      ( " ^ result ^ " ) " ^ remaining;;

let formatting_ok =
  all
    (fun value ->
      original_cc value strings value = replacement_cc value strings value &&
      original_case value ["zero";"rhs"] 1 =
        replacement_case value ["zero";"rhs"] 1 &&
      original_vardecl value "name" max_int =
        replacement_vardecl value "name" max_int &&
      original_glpk min_int value "D" "F" =
        replacement_glpk min_int value "D" "F" &&
      original_domain value "V" "B" "R" "T" =
        replacement_domain value "V" "B" "R" "T")
    strings;;

let rec range first last =
  if first > last then [] else first::range (first + 1) last;;

let rec do_list operation = function
  | [] -> ()
  | head::tail -> operation head; do_list operation tail;;

let original_f4_order () =
  let visits = ref [] in
  for i3 = 0 to 1 do
    for i4 = 0 to 1 do
      for i5 = 0 to 1 do
        for i6 = 0 to 1 do
          visits := (i3,i4,i5,i6)::!visits
        done
      done
    done
  done;
  List.rev !visits;;

let replacement_f4_order () =
  let visits = ref [] in
  do_list
    (fun i3 ->
      do_list
        (fun i4 ->
          do_list
            (fun i5 ->
              do_list
                (fun i6 -> visits := (i3,i4,i5,i6)::!visits)
                (range 0 1))
            (range 0 1))
        (range 0 1))
    (range 0 1);
  List.rev !visits;;

let original_hex_order () =
  let visits = ref [] in
  for i1 = 0 to 4 do
    for i2 = i1 to 4 do
      for i3 = i2 to 4 do
        visits := (i1,i2,i3)::!visits
      done
    done
  done;
  List.rev !visits;;

let replacement_hex_order () =
  let visits = ref [] in
  do_list
    (fun i1 ->
      do_list
        (fun i2 ->
          do_list
            (fun i3 -> visits := (i1,i2,i3)::!visits)
            (range i2 4))
        (range i1 4))
    (range 0 4);
  List.rev !visits;;

let iteration_ok =
  original_f4_order() = replacement_f4_order() &&
  original_hex_order() = replacement_hex_order() &&
  List.length (original_f4_order()) = 16 &&
  List.length (original_hex_order()) = 35;;

let list_alias_ok =
  List.flatten [[1;2];[];[3]] = List.concat [[1;2];[];[3]];;

type structure_datum = { structure_id : string; structure_enabled : bool };;

let original_structure_trace = ref [];;
let original_structure_emit name =
  original_structure_trace := name::!original_structure_trace;;
module Original_structure_effects = struct
  original_structure_emit "first";;
  original_structure_emit "second";;
  { structure_id = "discarded"; structure_enabled = false };;
end;;

let normalized_structure_trace = ref [];;
let normalized_structure_emit name =
  normalized_structure_trace := name::!normalized_structure_trace;;
module Normalized_structure_effects = struct
  let _ = normalized_structure_emit "first";;
  let _ = normalized_structure_emit "second";;
  let _ = { structure_id = "discarded"; structure_enabled = false };;
end;;

let structure_effects_ok =
  !original_structure_trace = ["second";"first"] &&
  !normalized_structure_trace = !original_structure_trace;;

let string_order_ok =
  List.sort (fun left right -> if left < right then -1 else 1) strings =
  List.sort String.compare strings;;

let () =
  if simple_formats_ok && formatting_ok && iteration_ok && list_alias_ok &&
     string_order_ok && structure_effects_ok
  then print_endline "NONLINEAR_BOUNDARY_COMPATIBILITY_OCAML_ORACLE_OK"
  else failwith "nonlinear boundary compatibility oracle";;
