type hol_type =
  | Tyvar of string
  | Tyapp of string * hol_type list;;

type term =
  | Var of string * hol_type
  | Const of string * hol_type
  | Comb of term * term
  | Abs of term * term;;

let rec list_compare compare_element left right =
  match left,right with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | x::xs,y::ys ->
      let result = compare_element x y in
      if result = 0 then list_compare compare_element xs ys else result;;

let pair_compare compare_left compare_right (x1,y1) (x2,y2) =
  let result = compare_left x1 x2 in
  if result = 0 then compare_right y1 y2 else result;;

let rec type_compare left right =
  match left,right with
  | Tyvar x,Tyvar y -> String.compare x y
  | Tyvar _,Tyapp _ -> -1
  | Tyapp(x,xs),Tyapp(y,ys) ->
      pair_compare String.compare (list_compare type_compare) (x,xs) (y,ys)
  | Tyapp _,Tyvar _ -> 1;;

let rec term_compare left right =
  match left,right with
  | Var(x,ty),Var(y,uy) -> pair_compare String.compare type_compare (x,ty) (y,uy)
  | Var _,_ -> -1
  | Const(x,ty),Const(y,uy) -> pair_compare String.compare type_compare (x,ty) (y,uy)
  | Const _,Var _ -> 1
  | Const _,_ -> -1
  | Comb(x,y),Comb(u,v) -> pair_compare term_compare term_compare (x,y) (u,v)
  | Comb _,Var _ | Comb _,Const _ -> 1
  | Comb _,Abs _ -> -1
  | Abs(x,y),Abs(u,v) -> pair_compare term_compare term_compare (x,y) (u,v)
  | Abs _,_ -> 1;;

let sign value = if value < 0 then -1 else if value > 0 then 1 else 0;;

let rec pairs values =
  match values with
  | [] -> []
  | head::tail ->
      List.map (fun value -> head,value) values @ pairs tail;;

let rec sort predicate values =
  match values with
  | [] -> []
  | pivot::rest ->
      let greater,lesser = List.partition (predicate pivot) rest in
      sort predicate lesser @ (pivot::sort predicate greater);;

let rec uniq values =
  match values with
  | x::(y::_ as tail) ->
      let tail' = uniq tail in
      if x = y then tail' else x::tail'
  | _ -> values;;

let setify predicate values = uniq (sort predicate values);;

let original_update_all update values =
  let state = ref values in
  for i = 0 to List.length values - 1 do
    state := update i !state
  done;
  !state;;

let replacement_update_all update values =
  let state = ref values in
  let n = List.length values in
  let rec update_all i =
    if i = n then ()
    else (state := update i !state; update_all (i + 1)) in
  update_all 0;
  !state;;

let hash_with character_code s =
  let rec explode index =
    if index = String.length s then []
    else String.make 1 (String.get s index) :: explode (index + 1) in
  let rec hashll values =
    match values with
    | [] -> 0
    | h::t ->
        (character_code (String.get h 0) + 1223 * hashll t) mod 8831 in
  hashll (explode 0);;

let original_structure_effects = ref [];;
module Original_structure_effects = struct
  let emit value =
    original_structure_effects := value::!original_structure_effects;;
  emit 1;;
  emit 2;;
end;;

let normalized_structure_effects = ref [];;
module Normalized_structure_effects = struct
  let emit value =
    normalized_structure_effects := value::!normalized_structure_effects;;
  let _ = emit 1;;
  let _ = emit 2;;
end;;

let aty = Tyvar "A";;
let bty = Tyapp("fun",[aty;Tyvar "B"]);;
let x = Var("x",aty);;
let y = Var("y",aty);;
let c = Const("c",bty);;
let terms = [x;y;c;Comb(c,x);Abs(x,y);Comb(c,y)];;
let compare_ok =
  List.for_all
    (fun (left,right) ->
       sign (Stdlib.compare left right) = sign (term_compare left right))
    (pairs terms);;
let setify_ok =
  setify (fun left right -> Stdlib.compare left right <= 0)
    [y;x;Comb(c,x);x;c] =
  setify (fun left right -> term_compare left right < 0)
    [y;x;Comb(c,x);x;c] &&
  setify (fun left right -> Stdlib.compare left right <= 0)
    [("z",x);("a",y);("a",x);("a",y)] =
  setify
    (fun left right ->
       pair_compare String.compare term_compare left right <= 0)
    [("z",x);("a",y);("a",x);("a",y)];;
let update index state =
  List.mapi (fun i value -> if i = index then value + i + 1 else value) state;;
let loop_ok =
  List.for_all
    (fun values ->
       original_update_all update values = replacement_update_all update values)
    [[];[0];[0;10];[0;10;20;30]];;
let char_ok =
  let rec check code =
    code = 256 ||
    (int_of_char (char_of_int code) = Char.code (char_of_int code) &&
     check (code + 1)) in
  check 0;;
let hash_ok =
  List.for_all
    (fun value -> hash_with int_of_char value = hash_with Char.code value)
    ["";"a";"abc";"Flyspeck";"\000\127\255"];;
let structure_effect_ok =
  !original_structure_effects = [2;1] &&
  !normalized_structure_effects = !original_structure_effects;;

let () =
  if compare_ok && setify_ok && loop_ok && char_ok && hash_ok &&
     structure_effect_ok then
    print_endline "FLYSPECK_BOUNDARY_COMPATIBILITY_OCAML_ORACLE_OK"
  else failwith "Flyspeck boundary compatibility OCaml oracle failed";;
