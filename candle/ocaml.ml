exception Sys_error of string;;
exception Invalid_argument of string;;
exception End_of_file;;
exception Not_found;;

let pp_exn e =
  match e with
  | Invalid_argument s ->
     Pretty_printer.app_block "Invalid_argument" [Pretty_printer.pp_string s]
  | Sys_error s ->
     Pretty_printer.app_block "Sys_error" [Pretty_printer.pp_string s]
  | End_of_file -> Pretty_printer.token "End_of_file"
  | Not_found -> Pretty_printer.token "Not_found"
  | _ -> pp_exn e;;

let invalid_arg s = raise (Invalid_argument s);;

let open_in name = try Text_io.openIn name
  with Text_io.Bad_file_name -> raise (Sys_error ("open_in " ^ name))
;;

let open_out name = Text_io.openOut name;;

let output_string s fd = Text_io.output s fd;;

let close_in fd = Text_io.closeIn fd;;

let close_out fd = Text_io.closeOut fd;;

let input_line fd =
  match Text_io.inputLine fd with
  | Some l -> l
  | None -> raise End_of_file
;;

(* There isn't really a maximal integer since we have bignums. *)
let max_int = 2305843009213693951  (* 2^61 - 1 *)
let float_of_int x = Cake.Double.fromInt x
let int_of_float x = Cake.Double.toInt x
let floor x = Cake.Double.floor x

(* General helpers. May be moved. *)
module Candle = struct
  let ordering_to_int cmp x y =
    match cmp x y with
    | Equal -> 0
    | Less -> ~-1
    | Greater -> 1
  ;;
  let int_to_ordering cmp x y =
    let r = cmp x y in
    if r < 0 then Less
    else if r > 0 then Greater
    else Equal
end;;

module Pair = struct
  let compare cmpa cmpb (a1, b1) (a2, b2) =
    let ar = cmpa a1 a2 in
    if ar = 0 then cmpb b1 b2 else ar
end;;

module Int = struct
  let compare x y =
    if x < y then -1 else if x > y then 1 else 0
  let max x y = if x > y then x else y
  let to_string x = Cake.Int.toString x
end;;

module Float = struct
  type float = double
  let zero = Cake.Double.fromInt 0
  let one = Cake.Double.fromInt 1
  let minus_one = Cake.Double.fromInt ~-1
  let sqrt x = Cake.Double.sqrt x
  let abs x = Cake.Double.abs x
  let compare x y =
    if Cake.Double.(<) x y then -1
    else if Cake.Double.(>) x y then 1
    else 0
  let of_string s = match Cake.Double.fromString s with
    | None -> failwith "Float.of_string"
    | Some x -> x

  (* OCaml [frexp] is exactly a decomposition of the IEEE-754 encoding.  Use
     CakeML's proved field extractors/reconstructor instead of a host FFI.
     Normal results have magnitude in [0.5,1); zero retains its sign; and
     infinities/NaNs are returned unchanged with exponent zero. *)
  let frexp value =
    let exponent = Cake.Word64.toInt (Cake.Double.exponent value) in
    let significand = Cake.Word64.toInt (Cake.Double.significand value) in
    let sign = Cake.Double.sign value in
    if exponent = 0 then
      if significand = 0 then value, 0
      else
        let rec highest_bit index bits =
          if bits < 2 then index else highest_bit (index + 1) (bits / 2) in
        let rec power_two exponent accumulator =
          if exponent = 0 then accumulator
          else power_two (exponent - 1) (2 * accumulator) in
        let bit = highest_bit 0 significand in
        let normalized =
          significand * power_two (52 - bit) 1 - power_two 52 1 in
        (Cake.Double.construct sign (Cake.Word64.fromInt 1022)
           (Cake.Word64.fromInt normalized),
         bit - 1073)
    else if exponent = 2047 then value, 0
    else
      (Cake.Double.construct sign (Cake.Word64.fromInt 1022)
         (Cake.Double.significand value),
       exponent - 1022)
end;;

let frexp = Float.frexp;;

type float = Float.float;;

(* Selected Flyspeck sources qualify the ordinary OCaml I/O and square-root
   operations through [Stdlib].  Deliberately omit polymorphic [compare]: each
   selected comparison must be normalized to a type-specific comparator. *)
module Stdlib = struct
  let compare left right =
    if left = right then 0
    else failwith
      "Stdlib.compare: polymorphic ordering is unavailable; use an explicit comparator"
  let open_in = open_in
  let open_out = open_out
  let input_line = input_line
  let close_in = close_in
  let close_out = close_out
  let output_string = output_string
  let sqrt = Float.sqrt
end;;

module List = struct
  let fold_left f init xs = Cake.List.foldl (fun x y -> f y x) init xs
  let fold_right f xs init = Cake.List.foldr f init xs
  let find f l = match Cake.List.find f l with
    | None -> raise Not_found
    | Some x -> x
  let nth l i =
    if i < 0 then raise (Invalid_argument "List.nth")
    else if i >= Cake.List.length l then raise (Failure "List.nth")
    else Cake.List.nth l i
  let for_all f l = Cake.List.all f l
  let iter f xs = Cake.List.app f xs
  let hd = function
    | [] -> failwith "List.hd"
    | h :: _ -> h
  let rec assoc key = function
    | [] -> raise Not_found
    | (k, v) :: rest -> if k = key then v else assoc key rest
  let rec mem_assoc key = function
    | [] -> false
    | (k, _) :: rest -> k = key || mem_assoc key rest
  let filter f l = Cake.List.filter f l
  let partition f l = Cake.List.partition f l
  let sort cmp xs = Cake.List.sort (fun x y -> cmp x y < 0) xs
  let length xs = Cake.List.length xs
  let map f xs = Cake.List.map f xs
  let rec map2 f xs ys =
    match xs, ys with
    | [], [] -> []
    | x :: xs', y :: ys' -> f x y :: map2 f xs' ys'
    | _ -> invalid_arg "map2: lists must have equal length"
  let mem a set = Cake.List.member a set
  let rev xs = Cake.List.rev xs
  let concat xss = Cake.List.concat xss
  let rev_append l1 l2 =
    let rec aux acc l =
      match l with
        [] -> acc
      | h::t -> aux (h::acc) t in
    aux l2 l1;;
  let exists f xs = Cake.List.exists f xs
  let rec compare cmp xs ys =
    match (xs, ys) with
    | ([], []) -> 0
    | ([], l2) -> -1
    | (l1, []) -> 1
    | (x::l1, y::l2) ->
       let r = cmp x y in
       if r = 0 then compare cmp l1 l2 else r
end;;

module Char = struct
  let compare c1 c2 =
    if Cake.Char.(<) c1 c2 then -1
    else if Cake.Char.(>) c1 c2 then 1
    else 0
  let code c = Cake.Char.ord c
  let chr i = try Cake.Char.chr i
    with Chr -> raise (Invalid_argument "Char.chr")
end;;

module String = struct
  let make n c =
    if n < 0 then raise (Invalid_argument "String.make")
    else Cake.String.implode (Cake.List.tabulate n (fun _ -> c))
  let sub s pos len = try Cake.String.substring s pos len
    with Subscript -> raise (Invalid_argument "String.sub")
  let get s i = try Cake.String.sub s i
    with Subscript -> raise (Invalid_argument "String.get")
  let length s = Cake.String.size s;;
  let compare x y = Candle.ordering_to_int Cake.String.compare x y
  let escaped s = Cake.String.escape_str s
  let concat sep ss = Cake.String.concatWith sep ss
  (* TODO Painful use of Word64s which are always boxed; prime candidate for
     writing in Pancake that's embedded, once that's possible. At that point,
     it should probably move to CakeML as well. *)
  (* Adapted from http://www.cse.yorku.ca/~oz/hash.html (djb2) *)
  let hash s =
    let times_33 w = (Cake.Word64.(+) (Cake.Word64.(<<) w 5) w) in
    let step char hash =
      Cake.Word64.xorb (times_33 hash) (Cake.Word64.fromInt (Cake.Char.ord char)) in
    Cake.Word64.toInt (Cake.List.foldl step (Cake.Word64.fromInt 5381) (Cake.String.explode s));;
end;;

(* OCaml's mutable string buffer is distinct from the token queue named
   [Buffer] in Candle's REPL boot image.  Flyspeck's strictbuild reader and
   serializer need only this small, pure source-backed subset. *)
module Buffer = struct
  type t = string list ref

  let create capacity =
    if capacity < 0 then invalid_arg "Buffer.create"
    else ref ([] : string list)

  let add_string buffer value =
    buffer := value :: !buffer

  let add_char buffer value =
    add_string buffer (String.make 1 value)

  let rec add_channel buffer channel count =
    if count < 0 then invalid_arg "Buffer.add_channel"
    else if count = 0 then ()
    else
      match Text_io.input1 channel with
      | None -> raise End_of_file
      | Some value ->
         add_char buffer value;
         add_channel buffer channel (count - 1)

  let contents buffer =
    String.concat "" (List.rev !buffer)

  let reset buffer =
    buffer := []
end;;

(* Pure source-level MD5 for the selected OCaml [Digest] surface.  This avoids
   adding a host hashing FFI.  The implementation uses virtual MD5 padding, so
   [Digest.string] does not allocate a second padded copy of its input. *)
module Digest = struct
  type t = string

  let md5_mask value = value land 0xffffffff
  let md5_add left right = md5_mask (left + right)
  let md5_rotate_left value count =
    md5_mask ((value lsl count) lor (value lsr (32 - count)))

  let md5_shifts = Cake.Array.fromList
    [7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22; 7; 12; 17; 22;
     5; 9; 14; 20; 5; 9; 14; 20; 5; 9; 14; 20; 5; 9; 14; 20;
     4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23; 4; 11; 16; 23;
     6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21; 6; 10; 15; 21]

  let md5_constants = Cake.Array.fromList
    [0xd76aa478; 0xe8c7b756; 0x242070db; 0xc1bdceee;
     0xf57c0faf; 0x4787c62a; 0xa8304613; 0xfd469501;
     0x698098d8; 0x8b44f7af; 0xffff5bb1; 0x895cd7be;
     0x6b901122; 0xfd987193; 0xa679438e; 0x49b40821;
     0xf61e2562; 0xc040b340; 0x265e5a51; 0xe9b6c7aa;
     0xd62f105d; 0x02441453; 0xd8a1e681; 0xe7d3fbc8;
     0x21e1cde6; 0xc33707d6; 0xf4d50d87; 0x455a14ed;
     0xa9e3e905; 0xfcefa3f8; 0x676f02d9; 0x8d2a4c8a;
     0xfffa3942; 0x8771f681; 0x6d9d6122; 0xfde5380c;
     0xa4beea44; 0x4bdecfa9; 0xf6bb4b60; 0xbebfbc70;
     0x289b7ec6; 0xeaa127fa; 0xd4ef3085; 0x04881d05;
     0xd9d4d039; 0xe6db99e5; 0x1fa27cf8; 0xc4ac5665;
     0xf4292244; 0x432aff97; 0xab9423a7; 0xfc93a039;
     0x655b59c3; 0x8f0ccc92; 0xffeff47d; 0x85845dd1;
     0x6fa87e4f; 0xfe2ce6e0; 0xa3014314; 0x4e0811a1;
     0xf7537e82; 0xbd3af235; 0x2ad7d2bb; 0xeb86d391]

  let md5_word byte_at block word_index =
    let offset = block + (4 * word_index) in
    byte_at offset lor
    (byte_at (offset + 1) lsl 8) lor
    (byte_at (offset + 2) lsl 16) lor
    (byte_at (offset + 3) lsl 24)

  let md5_transform byte_at block (a0, b0, c0, d0) =
    let rec rounds index a b c d =
      if index = 64 then
        (md5_add a0 a, md5_add b0 b, md5_add c0 c, md5_add d0 d)
      else
        let (mixed, word_index) =
          if index < 16 then
            ((b land c) lor ((lnot b) land d), index)
          else if index < 32 then
            ((d land b) lor ((lnot d) land c), (5 * index + 1) mod 16)
          else if index < 48 then
            (b lxor c lxor d, (3 * index + 5) mod 16)
          else
            (c lxor (b lor (lnot d)), (7 * index) mod 16) in
        let sum = md5_mask
          (a + md5_mask mixed + md5_word byte_at block word_index +
           Cake.Array.sub md5_constants index) in
        let next_b = md5_add b
          (md5_rotate_left sum (Cake.Array.sub md5_shifts index)) in
        rounds (index + 1) d next_b b c in
    rounds 0 a0 b0 c0 d0

  let md5_raw source =
    let source_length = String.length source in
    let total_length = ((source_length + 72) / 64) * 64 in
    let bit_length = source_length * 8 in
    let length_offset = total_length - 8 in
    let byte_at index =
      if index < source_length then Char.code (String.get source index)
      else if index = source_length then 128
      else if index < length_offset then 0
      else (bit_length lsr (8 * (index - length_offset))) land 255 in
    let rec blocks offset state =
      if offset = total_length then state
      else blocks (offset + 64) (md5_transform byte_at offset state) in
    let (a, b, c, d) =
      blocks 0 (0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476) in
    let pack_word word =
      String.concat ""
        [String.make 1 (Char.chr (word land 255));
         String.make 1 (Char.chr ((word lsr 8) land 255));
         String.make 1 (Char.chr ((word lsr 16) land 255));
         String.make 1 (Char.chr ((word lsr 24) land 255))] in
    String.concat "" [pack_word a; pack_word b; pack_word c; pack_word d]

  let string source = md5_raw source

  let file path =
    let channel = open_in path in
    let contents =
      try Text_io.inputAll channel
      with error ->
        close_in channel;
        raise error in
    close_in channel;
    string contents

  let to_hex digest =
    if String.length digest <> 16 then invalid_arg "Digest.to_hex"
    else
      let digits = "0123456789abcdef" in
      let byte_to_hex value =
        let byte = Char.code value in
        String.concat ""
          [String.make 1 (String.get digits (byte / 16));
           String.make 1 (String.get digits (byte mod 16))] in
      let rec encode index result =
        if index < 0 then String.concat "" result
        else encode (index - 1) (byte_to_hex (String.get digest index) :: result) in
      encode 15 []

  let compare left right = String.compare left right
end;;

(* A source-level compatibility implementation for the exact [Str] surface in
   the direct Flyspeck full-build graph.  This is deliberately pure: accepting
   [str.cma] must not turn into a host dynamic-loader or FFI capability.

   The supported regular-expression syntax is the subset exercised by the
   pinned source: literals, dot, character classes (including negation and
   ranges), the [*], [+], and [?] quantifiers, and beginning/end anchors.
   OCaml Str's escaped grouping, alternation, and back-reference syntax fails
   explicitly instead of being silently misinterpreted. *)
module Str = struct
  type atom =
    | Str_char of char
    | Str_any
    | Str_class of bool * char list
    | Str_start
    | Str_end

  type quantifier =
    | Str_once
    | Str_star
    | Str_plus
    | Str_optional

  type regexp = Str_regexp of (atom * quantifier) list

  let invalid_regexp () = invalid_arg "Str.regexp: unsupported or malformed pattern"

  let regexp pattern =
    let pattern_length = String.length pattern in
    let rec add_range first last chars =
      let first_code = Char.code first in
      let last_code = Char.code last in
      let rec add code acc =
        if code > last_code then acc
        else add (code + 1) (Char.chr code :: acc) in
      if first_code > last_code then invalid_regexp ()
      else add first_code chars in
    let read_class_char index =
      if index >= pattern_length then invalid_regexp ()
      else
        let first = String.get pattern index in
        if first = '\\' then
          if index + 1 >= pattern_length then invalid_regexp ()
          else (String.get pattern (index + 1), index + 2)
        else (first, index + 1) in
    let rec parse_class negated chars index =
      if index >= pattern_length then invalid_regexp ()
      else if String.get pattern index = ']' then
        if chars = [] then invalid_regexp ()
        else (Str_class (negated, List.rev chars), index + 1)
      else
        let first, next = read_class_char index in
        if next + 1 < pattern_length &&
           String.get pattern next = '-' &&
           String.get pattern (next + 1) <> ']' then
          let last, after = read_class_char (next + 1) in
          parse_class negated (add_range first last chars) after
        else
          parse_class negated (first :: chars) next in
    let quantifier atom index =
      if index >= pattern_length then (Str_once, index)
      else
        let candidate = String.get pattern index in
        let repeat, next =
          if candidate = '*' then (Str_star, index + 1)
          else if candidate = '+' then (Str_plus, index + 1)
          else if candidate = '?' then (Str_optional, index + 1)
          else (Str_once, index) in
        match atom, repeat with
        | (Str_start, Str_once) -> (repeat, next)
        | (Str_end, Str_once) -> (repeat, next)
        | (Str_start, _) -> invalid_regexp ()
        | (Str_end, _) -> invalid_regexp ()
        | _ -> (repeat, next) in
    let rec parse pieces index =
      if index >= pattern_length then Str_regexp (List.rev pieces)
      else
        let current = String.get pattern index in
        let atom, next =
          if current = '[' then
            let class_start = index + 1 in
            if class_start < pattern_length &&
               String.get pattern class_start = '^' then
              parse_class true [] (class_start + 1)
            else parse_class false [] class_start
          else if current = '\\' then
            if index + 1 >= pattern_length then invalid_regexp ()
            else
              let escaped = String.get pattern (index + 1) in
              if List.mem escaped ['('; ')'; '|'; '1'; '2'; '3'; '4';
                                   '5'; '6'; '7'; '8'; '9'] then
                invalid_regexp ()
              else (Str_char escaped, index + 2)
          else if current = '.' then (Str_any, index + 1)
          else if current = '^' then (Str_start, index + 1)
          else if current = '$' then (Str_end, index + 1)
          else if current = '*' || current = '+' || current = '?' then
            invalid_regexp ()
          else (Str_char current, index + 1) in
        let repeat, after = quantifier atom next in
        parse ((atom, repeat) :: pieces) after in
    parse [] 0

  let atom_advance atom text position =
    let text_length = String.length text in
    match atom with
    | Str_start -> if position = 0 then Some position else None
    | Str_end -> if position = text_length then Some position else None
    | Str_char expected ->
       if position < text_length && String.get text position = expected then
         Some (position + 1)
       else None
    | Str_any ->
       if position < text_length && String.get text position <> '\n' then
         Some (position + 1)
       else None
    | Str_class (negated, chars) ->
       if position >= text_length then None
       else
         let present = List.mem (String.get text position) chars in
         if present <> negated then Some (position + 1) else None

  let rec match_pieces pieces text position =
    match pieces with
    | [] -> Some position
    | (atom, repeat) :: rest ->
       let rec try_positions = function
         | [] -> None
         | candidate :: candidates ->
            (match match_pieces rest text candidate with
             | Some ending -> Some ending
             | None -> try_positions candidates) in
       let rec consume candidate positions =
         match atom_advance atom text candidate with
         | Some next ->
            if next > candidate then consume next (next :: positions)
            else positions
         | None -> positions in
       match repeat with
       | Str_once ->
          (match atom_advance atom text position with
           | Some next -> match_pieces rest text next
           | None -> None)
       | Str_optional ->
          (match atom_advance atom text position with
           | Some next -> try_positions [next; position]
           | None -> match_pieces rest text position)
       | Str_star -> try_positions (consume position [position])
       | Str_plus ->
          (match atom_advance atom text position with
           | Some next ->
              if next > position then try_positions (consume next [next])
              else None
           | None -> None)

  let match_at (Str_regexp pieces) text position =
    match_pieces pieces text position

  let string_match expression text position =
    if position < 0 || position > String.length text then
      invalid_arg "Str.string_match"
    else
      match match_at expression text position with
      | Some _ -> true
      | None -> false

  let search_forward expression text start =
    let text_length = String.length text in
    let rec search position =
      if position > text_length then None
      else
        match match_at expression text position with
        | Some ending -> Some (position, ending)
        | None -> search (position + 1) in
    if start < 0 || start > text_length then invalid_arg "Str.search_forward"
    else search start

  let split expression text =
    let text_length = String.length text in
    let rec drop_empty_prefix = function
      | "" :: fields -> drop_empty_prefix fields
      | fields -> fields in
    let trim_empty_edges fields =
      let without_leading = drop_empty_prefix fields in
      List.rev (drop_empty_prefix (List.rev without_leading)) in
    let add_field start ending fields =
      String.sub text start (ending - start) :: fields in
    let finish fields = trim_empty_edges (List.rev fields) in
    let rec fields field_start search_start result =
      if search_start > text_length then
        finish (add_field field_start text_length result)
      else
        match search_forward expression text search_start with
        | None -> finish (add_field field_start text_length result)
        | Some (match_start, match_end) ->
           let result' = add_field field_start match_start result in
           if match_end > match_start then
             fields match_end match_end result'
           else if match_start < text_length then
             fields match_start (match_start + 1) result'
           else finish result' in
    fields 0 0 []

  let global_replace expression replacement text =
    let rec literal_replacement index =
      if index >= String.length replacement then ()
      else if String.get replacement index = '\\' then
        invalid_arg "Str.global_replace: replacement back-references unsupported"
      else literal_replacement (index + 1) in
    let text_length = String.length text in
    let rec replace copied search_start result =
      match search_forward expression text search_start with
      | None ->
         String.concat ""
           (List.rev (String.sub text copied (text_length - copied) :: result))
      | Some (match_start, match_end) ->
         if match_end = match_start then
           invalid_arg "Str.global_replace: empty matches unsupported"
         else
           let prefix = String.sub text copied (match_start - copied) in
           replace match_end match_end (replacement :: prefix :: result) in
    let _ = literal_replacement 0 in
    replace 0 0 []

  let first_chars text count = String.sub text 0 count
end;;

module Array = struct
  let make n x = Cake.Array.array n x
  let init n f =
    if n < 0 then invalid_arg "Array.init"
    else Cake.Array.tabulate n f
  let length a = Cake.Array.length a
  let set a n x = try Cake.Array.update a n x
    with Subscript -> raise (Invalid_argument "Array.set")
  let get a n = try Cake.Array.sub a n
    with Subscript -> raise (Invalid_argument "Array.get")
  let fold_left f init a = Cake.Array.foldl (fun x y -> f y x) init a
  let of_list l = Cake.Array.fromList l
  let map f a =
    Cake.Array.tabulate (Cake.Array.length a) (fun i -> f (Cake.Array.sub a i))
end;;

module Printexc = struct
  let to_string (e: exn) = "TODO stub (Printexc.to_string)"
end;;

module Format = struct
  type formatter = Pretty_imp.state;;

  let set_margin n =
    if n < 1 then failwith "set_margin: must be positive";
    Pretty.margin := n
  ;;

  let pp_print_as = Pretty_imp.print_as;;
  let pp_print_string = Pretty_imp.print_string;;
  let pp_print_break = Pretty_imp.print_break;;
  let pp_print_space fmt () = Pretty_imp.print_space fmt;;
  let pp_print_newline fmt () = Pretty_imp.print_newline fmt;;

  let pp_open_box = Pretty_imp.open_block;;
  let pp_open_hbox fmt () = Pretty_imp.open_hblock fmt;;
  let pp_open_vbox = Pretty_imp.open_vblock;;
  let pp_open_hvbox = Pretty_imp.open_hvblock;;
  let pp_close_box fmt () = Pretty_imp.close_block fmt;;

  let pp_get_max_boxes (fmt:formatter) () = ~-1;;  (* TODO stub *)
  let pp_set_max_boxes (fmt:formatter) (i:int) = ();;  (* TODO stub *)
  let set_max_boxes (i:int) = ();;  (* TODO stub *)

  (* Functions that print to stdout: *)

  let print_string = Pretty.print_stdout pp_print_string;;
  let print_break l i =
    Pretty.print_stdout (fun s (l,i) -> pp_print_break s l i) (l, i);;
  let print_space () = Pretty.print_stdout pp_print_space ();;
  let print_newline () = Pretty.print_stdout pp_print_newline ();;
  let print_flush () = ();; (* TODO? stub *)

  let open_box = Pretty.print_stdout pp_open_box;;
  let open_hbox () = Pretty.print_stdout pp_open_hbox ();;
  let open_vbox = Pretty.print_stdout pp_open_vbox;;
  let open_hvbox = Pretty.print_stdout pp_open_hvbox;;
  let close_box () = Pretty.print_stdout pp_close_box ();;
end;;

let print_string s = Format.print_string s;;
let print_newline () = Format.print_newline ();;
let print_endline s = print_string s; print_newline ();;

(* TODO Move Random module to CakeML basis. *)
module Random = struct
  (* TODO This should probably be a local in CakeML *)
  let state = ref 1;;

  let init i = state := i;;

  let bits () =
    (* Parameters permanently borrowed from glibc's stdlib/random_r.c *)
    let a = 1103515245 in
    let c = 12345 in
    let m = 2147483648 (* 2^31 *) in
    let next_s = (a * !state + c) mod m in
    state := next_s; next_s;;

  let int bound =
    if bound <= 0 || bound >= 1073741824 (* 2^30 *)
    then raise (Invalid_argument "Random.int")
    else bits () mod bound;;
end;;

module Hashtbl = struct
  (* CakeML intentionally has no polymorphic hash or ordering operation.  The
     unary OCaml constructor therefore uses an equality-backed association
     list.  Performance-sensitive Candle code can opt into the proved CakeML
     hashtable with explicit hash/order functions via [create_ordered]. *)
  type ('a, 'b) t =
    Linear of (('a * 'b) list ref)
  | Ordered of (('a, 'b) Cake.Hashtable.hashtable);;

  let create capacity =
    if capacity < 0 then invalid_arg "Hashtbl.create"
    else Linear (ref [])

  let create_ordered size hash order =
    if size < 0 then invalid_arg "Hashtbl.create_ordered"
    else Ordered
      (Cake.Hashtable.empty size hash (Candle.int_to_ordering order))

  let hash _ =
    failwith
      "Hashtbl.hash: polymorphic hashing is unavailable; use an explicit hash"

  let rec find_linear key entries =
    match entries with
      [] -> raise Not_found
    | (entry_key, value)::rest ->
        if entry_key = key then value else find_linear key rest

  let find table key =
    match table with
      Linear entries -> find_linear key !entries
    | Ordered ordered ->
        (match Cake.Hashtable.lookup ordered key with
           None -> raise Not_found
         | Some value -> value)

  let mem table key =
    try let _ = find table key in true with Not_found -> false

  let add table key value =
    match table with
      Linear entries -> entries := (key, value) :: !entries
    | Ordered ordered -> Cake.Hashtable.insert ordered key value

  let rec replace_linear key value entries =
    match entries with
      [] -> [key, value]
    | (entry_key, entry_value)::rest ->
        if entry_key = key then (key, value)::rest
        else (entry_key, entry_value)::replace_linear key value rest

  let replace table key value =
    match table with
      Linear entries -> entries := replace_linear key value !entries
    | Ordered ordered -> Cake.Hashtable.insert ordered key value

  let rec remove_linear key entries =
    match entries with
      [] -> []
    | (entry_key, value)::rest ->
        if entry_key = key then rest
        else (entry_key, value)::remove_linear key rest

  let remove table key =
    match table with
      Linear entries -> entries := remove_linear key !entries
    | Ordered ordered -> Cake.Hashtable.delete ordered key

  let clear table =
    match table with
      Linear entries -> entries := []
    | Ordered ordered -> Cake.Hashtable.clear ordered

  let length table =
    match table with
      Linear entries -> Cake.List.length !entries
    | Ordered ordered ->
        Cake.List.length (Cake.Hashtable.toAscList ordered)

  let fold f table init =
    let entries =
      match table with
        Linear linear -> !linear
      | Ordered ordered -> Cake.Hashtable.toAscList ordered in
    Cake.List.foldl (fun (key,value) acc -> f key value acc) init entries
end;;

module Bytes = struct
  let length s = Cake.Word8_array.length s
  (* NOTE OCaml also raises Invalid_argument if  n > Sys.max_string_length;
       additionally, OCaml returns an uninitialized sequence with
       arbitrary bytes. *)
  let create n =
    if n < 0 then invalid_arg "Bytes.create: negative argument" else
      Cake.Word8_array.array n (Cake.Word8.fromInt 0)
  (* NOTE OCaml can raise Invalid_argument in get, set, blit_string.
       Unsure how the CakeML handle out-of-bounds accesses. *)
  let get s n = Cake.Word8_array.sub s n
  let set s n c = Cake.Word8_array.update s n c
  let blit_string src src_pos dst dst_pos len =
    Cake.Word8_array.copyVec src src_pos len dst dst_pos
  let to_string s = Cake.Word8_array.substring s 0 (length s)
end;;

module Sys = struct
  (*
     The release loader supplies these values from its hashed manifest rather
     than inheriting the host process environment.  Keep the allowlist small:
     Flyspeck only needs these names during the direct-source build, and an
     absent serialization entry must retain OCaml's [Not_found] behaviour.

     This is a source-level compatibility slice.  [file_exists] intentionally
     uses CakeML's verified TextIO-backed file predicate, so it covers ordinary
     files but not directories.  Directory queries remain a separate, open FFI
     contract instead of silently widening this predicate with shell access.
  *)
  let manifest_environment = ref ([] : (string * string) list)
  let manifest_cwd = ref (None : string option)

  let configure_manifest_environment cwd flyspeck_dir hollight_dir
                                         serialization_enabled =
    if cwd = "" || flyspeck_dir = "" || hollight_dir = "" then
      invalid_arg "Sys.configure_manifest_environment: empty path"
    else
      let bindings =
        [("FLYSPECK_DIR", flyspeck_dir);
         ("HOLLIGHT_DIR", hollight_dir)] in
      let bindings' =
        if serialization_enabled then
          ("FLYSPECK_SERIALIZATION", "1") :: bindings
        else bindings in
      manifest_cwd := Some cwd;
      manifest_environment := bindings';;

  let rec getenv_from_manifest name = function
    | [] -> raise Not_found
    | (key, value) :: rest ->
        if key = name then value else getenv_from_manifest name rest

  let getenv name = getenv_from_manifest name !manifest_environment

  let getcwd () =
    match !manifest_cwd with
    | None -> raise (Sys_error "Sys.getcwd: manifest environment not configured")
    | Some cwd -> cwd

  (* The selected proof route only mentions [Sys.chdir] inside the historical
     GLPK generator chain and the LP archive extractor.  The latter is removed
     by an authenticated source normalization; the former has no selected
     external caller.  Retain the name so those deferred function bodies type,
     but abort if the generator lane is unexpectedly entered. *)
  let chdir path =
    failwith ("Sys.chdir: disabled by the Flyspeck S3 runtime policy: " ^ path)

  let file_exists = isFile

  (* The compatibility target is the pinned OCaml differential oracle.  The
     suffix makes it explicit that this is Candle, while preserving the OCaml
     version probes used by Flyspeck. *)
  let ocaml_version = "4.14.1-candle"
  let word_size = 64

  let remove (s: string) = print "TODO Sys.remove (noop)\n"
  let command (s: string) =
    failwith ("Sys.command: disabled by the Flyspeck S3 runtime policy: " ^ s);;
  let time () =
    print_endline "TODO Sys.time (always returns 0)";
    Float.zero;;
end;;

(* The selected [compact] calls are performance hints.  Keep them deterministic
   and free of a new runtime/host inspection FFI.  The record-valued [Gc.stat]
   telemetry is removed by an exact, hash-bound selected-source normalization. *)
module Gc = struct
  let compact () = ();;
end;;

(* Direct Flyspeck uses [Unix.open_process_in] during strictbuild startup and
   reporting to obtain metadata from [date] and [whoami].  The release path
   substitutes manifest-hashed text files for those nondeterministic shell
   commands.  No ambient process execution is exposed.

   The four selected [Unix.gettimeofday] calls measure load-time self-tests or
   LP verification and use their differences only as reported telemetry.  The
   proof-producing functions and their results do not depend on the clock.
   Return a deterministic zero timestamp so those computations execute without
   adding a clock FFI; wall/RSS timing belongs to the authenticated external
   runner.  This is a selected-route telemetry substitution, not a general
   implementation of OCaml wall-clock semantics.  Other selected Unix
   operations stay fail-closed until their sandbox/refinement obligations are
   implemented. *)
let candle_unix_manifest_process_inputs =
  ref (None : (string * string) option);;

let candle_configure_manifest_process_inputs date_file user_file =
    if date_file = "" || user_file = "" then
      invalid_arg "candle_configure_manifest_process_inputs: empty path"
    else if not (Sys.file_exists date_file) || not (Sys.file_exists user_file) then
      invalid_arg "candle_configure_manifest_process_inputs: missing ordinary file"
    else candle_unix_manifest_process_inputs := Some (date_file, user_file);;

module Unix = struct
  let open_process_in command =
    match !candle_unix_manifest_process_inputs with
    | None -> failwith "Unix.open_process_in: manifest inputs not configured"
    | Some (date_file, user_file) ->
       if command = "date" then open_in date_file
       else if command = "whoami" then open_in user_file
       else failwith ("Unix.open_process_in: command not allowlisted: " ^ command)

  let close_process_in channel =
    close_in channel

  let open_process command =
    failwith ("Unix.open_process: disabled pending sandbox contract: " ^ command)

  let close_process channels =
    failwith "Unix.close_process: unavailable without an opened sandboxed process"

  let gettimeofday () =
    Float.zero

  let mkdir path mode =
    failwith ("Unix.mkdir: disabled pending filesystem contract: " ^ path)
end;;

(* Save the boot-library filename operations before the OCaml-compatible
   [Filename] module below shadows that module name. *)
let candle_filename_is_relative = Filename.isRelative
let candle_filename_concat = Filename.concat
let candle_filename_basename = Filename.basename
let candle_filename_dirname = Filename.dirname

module Filename = struct
  (* Preserve the filename operations supplied by Candle's verified boot
     library.  Defining this OCaml-compatibility module used to shadow those
     operations and retain only the two temporary-file stubs. *)
  let current_dir_name = "."
  let parent_dir_name = ".."
  let is_relative = candle_filename_is_relative
  let concat = candle_filename_concat
  let basename = candle_filename_basename
  let dirname = candle_filename_dirname

  let check_suffix name suffix =
    let name_len = String.length name in
    let suffix_len = String.length suffix in
    suffix_len <= name_len &&
    String.sub name (name_len - suffix_len) suffix_len = suffix

  let get_temp_dir_name () =
    print_endline "TODO Filename.get_temp_dir_name (always returns /tmp)";
    "/tmp"
  let temp_file prefix suffix =
    print_endline "TODO Filename.temp_file (just concats temp dir, prefix, suffix)";
    get_temp_dir_name () ^ prefix ^ suffix
end;;
