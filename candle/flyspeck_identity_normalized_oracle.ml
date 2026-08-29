(* Compiled Candle acceptance oracle for the normalized allocated-value blocks.
   This file intentionally contains no physical-equality operator. *)

let candle_identity_require condition =
  if condition then () else failwith "normalized identity oracle mismatch";;

let candle_identity_filter p l =
  let rec changed l =
    match l with
      [] -> None
    | h::t ->
        (match changed t with
           None -> if p h then None else Some t
         | Some t' -> if p h then Some(h::t') else Some t') in
  match changed l with None -> l | Some l' -> l';;

let candle_identity_partition p l =
  let rec part l =
    match l with
      [] -> [],[],true,true
    | h::t ->
        let yes,no,all_yes,all_no = part t in
        if p h then
          ((if all_yes then l else h::yes),no,all_yes,false)
        else
          (yes,(if all_no then l else h::no),false,all_no) in
  let yes,no,_,_ = part l in yes,no;;

let candle_identity_uniq l =
  let rec changed l =
    match l with
      x::(y::_ as t) ->
        (match changed t with
           None ->
             if Stdlib.compare x y = 0 then Some t else None
         | Some t' ->
             if Stdlib.compare x y = 0 then Some t' else Some(x::t'))
    | _ -> None in
  match changed l with None -> l | Some l' -> l';;

let candle_identity_qmap _ _ =
  failwith "Candle Flyspeck: qmap requires physical sharing observation";;

type ('a,'b) candle_identity_trie =
    Candle_identity_empty
  | Candle_identity_leaf of int * ('a * 'b) list
  | Candle_identity_branch of int * int * ('a,'b) candle_identity_trie *
      ('a,'b) candle_identity_trie;;

let candle_identity_undefine =
  let rec undefine_list_changed x l =
    match l with
      (a,b as ab)::t ->
        let c = Stdlib.compare x a in
        if c = 0 then Some t
        else if c < 0 then None else
        (match undefine_list_changed x t with
           None -> None
         | Some t' -> Some(ab::t'))
    | [] -> None in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und_changed t =
      match t with
        Candle_identity_leaf(h,l) when h = k ->
          (match undefine_list_changed x l with
             None -> None
           | Some l' ->
               Some(if l' = [] then Candle_identity_empty
                    else Candle_identity_leaf(h,l')))
      | Candle_identity_branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            (match und_changed l with
               None -> None
             | Some l' ->
                 Some(match l' with Candle_identity_empty -> r
                                    | _ -> Candle_identity_branch(p,b,l',r)))
          else
            (match und_changed r with
               None -> None
             | Some r' ->
                 Some(match r' with Candle_identity_empty -> l
                                    | _ -> Candle_identity_branch(p,b,l,r')))
      | _ -> None in
    fun t -> match und_changed t with None -> t | Some t' -> t';;

let candle_identity_input = [1;2;3;4;5;6];;
candle_identity_require
  (candle_identity_filter (fun x -> x mod 2 = 0) candle_identity_input =
   [2;4;6]);;
candle_identity_require
  (candle_identity_partition (fun x -> x mod 2 = 0) candle_identity_input =
   ([2;4;6],[1;3;5]));;
candle_identity_require
  (candle_identity_uniq [1;1;2;2;2;3] = [1;2;3]);;
let candle_identity_qmap_failed_closed =
  try ignore (candle_identity_qmap (fun x -> x + 1) candle_identity_input);
      false
  with Failure _ -> true;;
candle_identity_require candle_identity_qmap_failed_closed;;

let candle_identity_key = 17;;
let candle_identity_leaf =
  Candle_identity_leaf(Hashtbl.hash candle_identity_key,
                       [candle_identity_key,"value"]);;
candle_identity_require
  (candle_identity_undefine candle_identity_key candle_identity_leaf =
   Candle_identity_empty);;
candle_identity_require
  (candle_identity_undefine 99 candle_identity_leaf = candle_identity_leaf);;

let candle_identity_unsuppress _ =
  failwith "Candle Flyspeck: unsuppress requires physical string identity";;
let candle_identity_unsuppress_failed_closed =
  try candle_identity_unsuppress "x"; false with Failure _ -> true;;
candle_identity_require candle_identity_unsuppress_failed_closed;;

type candle_identity_var = Candle_identity_var of string * int;;
let candle_identity_binder = Candle_identity_var("x",0);;
let candle_identity_avoids =
  candle_identity_filter
    (fun y -> not (y = candle_identity_binder))
    [candle_identity_binder; Candle_identity_var("x",0);
     Candle_identity_var("x",1)];;
candle_identity_require
  (candle_identity_avoids = [Candle_identity_var("x",1)]);;

let candle_flyspeck_identity_normalized_oracle_ok = true;;
