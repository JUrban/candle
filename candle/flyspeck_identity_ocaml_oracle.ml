(* OCaml 4.14.1 differential oracle for the allocated-value normalizations.
   Physical equality appears only on the pinned reference side and in oracle
   assertions.  The normalized definitions themselves use explicit change
   results or deterministic rebuilding. *)

let fail label = failwith ("flyspeck identity oracle: " ^ label);;
let require label condition = if not condition then fail label;;

let rec original_filter p l =
  match l with
    [] -> l
  | h::t -> let t' = original_filter p t in
            if p h then if t' == t then l else h::t'
            else t';;

let normalized_filter p l =
  let rec changed l =
    match l with
      [] -> None
    | h::t ->
        (match changed t with
           None -> if p h then None else Some t
         | Some t' -> if p h then Some(h::t') else Some t') in
  match changed l with None -> l | Some l' -> l';;

let rec original_partition p l =
  match l with
    [] -> [],l
  | h::t -> let yes,no = original_partition p t in
            if p h then (if yes == t then l,[] else h::yes,no)
            else (if no == t then [],l else yes,h::no);;

let normalized_partition p l =
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

let rec original_uniq l =
  match l with
    x::(y::_ as t) -> let t' = original_uniq t in
                      if Stdlib.compare x y = 0 then t' else
                      if t' == t then l else x::t'
  | _ -> l;;

let normalized_uniq l =
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

let rec original_qmap f l =
  match l with
    h::t -> let h' = f h and t' = original_qmap f t in
            if h' == h && t' == t then l else h'::t'
  | _ -> l;;

let normalized_qmap _ _ =
  failwith "Candle Flyspeck: qmap requires physical sharing observation";;

type ('a,'b) oracle_trie =
    Oracle_empty
  | Oracle_leaf of int * ('a * 'b) list
  | Oracle_branch of int * int * ('a,'b) oracle_trie * ('a,'b) oracle_trie;;

let original_undefine =
  let rec undefine_list x l =
    match l with
      (a,b as ab)::t ->
        let c = Stdlib.compare x a in
        if c = 0 then t
        else if c < 0 then l else
        let t' = undefine_list x t in
        if t' == t then l else ab::t'
    | [] -> [] in
  fun x ->
    let k = Hashtbl.hash x in
    let rec und t =
      match t with
        Oracle_leaf(h,l) when h = k ->
          let l' = undefine_list x l in
          if l' == l then t
          else if l' = [] then Oracle_empty
          else Oracle_leaf(h,l')
      | Oracle_branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            let l' = und l in
            if l' == l then t
            else (match l' with Oracle_empty -> r
                               | _ -> Oracle_branch(p,b,l',r))
          else
            let r' = und r in
            if r' == r then t
            else (match r' with Oracle_empty -> l
                               | _ -> Oracle_branch(p,b,l,r'))
      | _ -> t in
    und;;

let normalized_undefine =
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
        Oracle_leaf(h,l) when h = k ->
          (match undefine_list_changed x l with
             None -> None
           | Some l' ->
               Some(if l' = [] then Oracle_empty else Oracle_leaf(h,l')))
      | Oracle_branch(p,b,l,r) when k land (b - 1) = p ->
          if k land b = 0 then
            (match und_changed l with
               None -> None
             | Some l' ->
                 Some(match l' with Oracle_empty -> r
                                      | _ -> Oracle_branch(p,b,l',r)))
          else
            (match und_changed r with
               None -> None
             | Some r' ->
                 Some(match r' with Oracle_empty -> l
                                      | _ -> Oracle_branch(p,b,l,r')))
      | _ -> None in
    fun t -> match und_changed t with None -> t | Some t' -> t';;

let valid_two_leaf_trie k1 v1 k2 v2 =
  let h1 = Hashtbl.hash k1 and h2 = Hashtbl.hash k2 in
  let differing = h1 lxor h2 in
  if differing = 0 then fail "unexpected hash collision";
  let bit = differing land (-differing) in
  let prefix = h1 land (bit - 1) in
  let t1 = Oracle_leaf(h1,[k1,v1]) and t2 = Oracle_leaf(h2,[k2,v2]) in
  if h1 land bit = 0 then Oracle_branch(prefix,bit,t1,t2)
  else Oracle_branch(prefix,bit,t2,t1);;

let trace_run f p input =
  let trace = ref [] in
  let predicate x = trace := x::!trace; p x in
  let result = f predicate input in result,List.rev !trace;;

let exception_trace f input =
  let trace = ref [] in
  let predicate x =
    trace := x::!trace;
    if x = 2 then failwith "predicate" else x mod 2 = 0 in
  try `Oracle_ok(f predicate input,List.rev !trace)
  with Failure message -> `Oracle_failure(message,List.rev !trace);;

let rec oracle_lists_at_most length =
  if length = 0 then [[]] else
  let shorter = oracle_lists_at_most (length - 1) in
  shorter @
  List.flatten
    (List.map
       (fun tail -> List.map (fun head -> head::tail) [0;1;2])
       shorter);;

let input = [1;2;3;4;5;6];;
let predicates =
  [(fun _ -> true); (fun _ -> false); (fun x -> x mod 2 = 0);
   (fun x -> x <> 3); (fun x -> x = 3)];;
List.iter
  (fun p ->
    let ro,to_ = trace_run original_filter p input
    and rn,tn = trace_run normalized_filter p input in
    require "filter structural result" (ro = rn);
    require "filter callback order" (to_ = tn);
    let po,tpo = trace_run original_partition p input
    and pn,tpn = trace_run normalized_partition p input in
    require "partition structural result" (po = pn);
    require "partition callback order" (tpo = tpn))
  predicates;;

List.iter
  (fun values ->
    List.iter
      (fun p ->
        let ro,to_ = trace_run original_filter p values
        and rn,tn = trace_run normalized_filter p values in
        require "exhaustive filter structural result" (ro = rn);
        require "exhaustive filter callback order" (to_ = tn);
        let po,tpo = trace_run original_partition p values
        and pn,tpn = trace_run normalized_partition p values in
        require "exhaustive partition structural result" (po = pn);
        require "exhaustive partition callback order" (tpo = tpn))
      predicates;
    require "exhaustive uniq structural result"
      (original_uniq values = normalized_uniq values);
    require "filter exception trace"
      (exception_trace original_filter values =
       exception_trace normalized_filter values);
    require "partition exception trace"
      (exception_trace original_partition values =
       exception_trace normalized_partition values))
  (oracle_lists_at_most 5);;

require "filter original all-kept sharing" (original_filter (fun _ -> true) input == input);;
require "filter normalized all-kept sharing" (normalized_filter (fun _ -> true) input == input);;
let oy,on = original_partition (fun _ -> true) input;;
let ny,nn = normalized_partition (fun _ -> true) input;;
require "partition original all-yes sharing" (oy == input && on = []);;
require "partition normalized all-yes sharing" (ny == input && nn = []);;
let oy,on = original_partition (fun _ -> false) input;;
let ny,nn = normalized_partition (fun _ -> false) input;;
require "partition original all-no sharing" (on == input && oy = []);;
require "partition normalized all-no sharing" (nn == input && ny = []);;

List.iter
  (fun values ->
    let original = original_uniq values
    and normalized = normalized_uniq values in
    require "uniq structural result" (original = normalized))
  [[]; [1]; [1;2;3]; [1;1;2]; [1;2;2;2;3]; [1;1;1]];;
let unique = [1;2;3;4];;
require "uniq original unchanged sharing" (original_uniq unique == unique);;
require "uniq normalized unchanged sharing" (normalized_uniq unique == unique);;

let q_original = original_qmap (fun x -> x) input in
require "qmap source sharing witness" (q_original == input);
require "qmap normalized call fails closed"
  (try ignore (normalized_qmap (fun x -> x) input); false
   with Failure _ -> true);;

let trie = valid_two_leaf_trie 7 "seven" 19 "nineteen" in
List.iter
  (fun key ->
    let original = original_undefine key trie
    and normalized = normalized_undefine key trie in
    require "undefine structural result" (original = normalized);
    if key <> 7 && key <> 19 then begin
      require "undefine original missing sharing" (original == trie);
      require "undefine normalized missing sharing" (normalized == trie)
    end)
  [7;19;1001];;

(* The relabel normalization is alpha-semantic, not exact name compatibility
   for arbitrary separately allocated equal Var nodes.  This model freezes the
   known divergence so the release must rely on selected-call fingerprints. *)
type oracle_var = Oracle_var of string * int;;
let binder = Oracle_var("x",0) in
let distinct_equal_binder = Oracle_var("x",0) in
let original_avoids = original_filter ((!=) binder) [binder;distinct_equal_binder] in
let normalized_avoids = normalized_filter (fun y -> not (y = binder))
  [binder;distinct_equal_binder] in
require "relabel physical model retains allocated equal copy"
  (original_avoids = [distinct_equal_binder]);
require "relabel structural model excludes equal copies" (normalized_avoids = []);;

print_endline "flyspeck-identity-ocaml-oracle: ok";;
