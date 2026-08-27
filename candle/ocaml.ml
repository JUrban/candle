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
end;;

type float = Float.float;;

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
  type ('a, 'b) t = ('a, 'b) Cake.Hashtable.hashtable
  (* Note that we additionally need to pass in hash and order to create *)
  let create size hash order =
    Cake.Hashtable.empty size hash (Candle.int_to_ordering order)
  let find tbl x =
    match Cake.Hashtable.lookup tbl x with
    | None -> raise Not_found
    | Some y -> y
  let replace tbl x y = Cake.Hashtable.insert tbl x y
  let remove tbl x = Cake.Hashtable.delete tbl x
  let fold f tbl init =
    Cake.List.foldl (fun (x,y) acc -> f x y acc) init (Cake.Hashtable.toAscList tbl)
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

  let file_exists = isFile

  (* The compatibility target is the pinned OCaml differential oracle.  The
     suffix makes it explicit that this is Candle, while preserving the OCaml
     version probes used by Flyspeck. *)
  let ocaml_version = "4.14.1-candle"

  let remove (s: string) = print "TODO Sys.remove (noop)\n"
  let command (s: string) =
    let slen = String.length s in
    (* slen + 1: null-terminated string; 2: status bytes *)
    let blen = Int.max 2 (slen + 1) in
    let bytes = Bytes.create blen in
    (* Avoid recomputing length by using blit_string instead of of_string *)
    let _ = Bytes.blit_string s 0 bytes 0 slen in
    let _ = Cake.Runtime.customFFI "system" bytes in
    let ret = Cake.Word8.toInt (Bytes.get bytes 0) in
    let _ =
      if 0 < ret
      then raise (Sys_error "Sys.command: no termination status for child")
      else () in
    Cake.Word8.toInt (Bytes.get bytes 1);;
  let time () =
    print_endline "TODO Sys.time (always returns 0)";
    Float.zero;;
end;;

(* Direct Flyspeck uses [Unix.open_process_in] during strictbuild startup and
   reporting to obtain metadata from [date] and [whoami].  The release path
   substitutes manifest-hashed text files for those nondeterministic shell
   commands.  No ambient process execution is exposed.  Other selected Unix
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
    failwith "Unix.gettimeofday: disabled pending clock contract"

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
