needs "candle/pft/pft.ml";;

let saved_ths = ref ([]: (string * thm) list);;
let rec saved_th_exists name = function
  | [] -> false
  | (name', _)::rest -> name = name' || saved_th_exists name rest;;
let save_th name th =
  if saved_th_exists name !saved_ths
  then failwith ("SAVE: duplicate name: " ^ name)
  else saved_ths := (name, th)::(!saved_ths);;
let rec load_th name = function
  | [] -> failwith ("LOAD: unknown name: " ^ name)
  | (name', th)::rest -> if name = name' then th else load_th name rest;;
let print_saved () =
  do_list (fun (s, th) ->
      print_endline (s ^ ": ");
      Pretty.print_stdout pp_print_colored_thm th;
      print_newline ()
    ) !saved_ths;;

let pft_max_string_length = ref (1024 * 1024);;
let pft_max_table_slots = ref 50000000;;
let pft_max_list_length = ref 10000000;;
let pft_axiom_policy = ref (fun (_: string) (_: term) -> false);;
let pft_axioms_used = ref ([]: (string * term) list);;
let pft_compute_context = ref (None: thm list option);;

let pft_atom_identity s = string_of_int (String.length s) ^ ":" ^ s;;

let rec pft_concat_identities f = function
  | [] -> ""
  | x::xs -> f x ^ pft_concat_identities f xs;;

let rec pft_type_identity ty =
  if is_vartype ty then "v" ^ pft_atom_identity (dest_vartype ty)
  else
    let name, args = dest_type ty in
    "t" ^ pft_atom_identity name ^ string_of_int (length args) ^ "[" ^
    pft_concat_identities pft_type_identity args ^ "]";;

let rec pft_bound_index tm env index =
  match env with
  | [] -> None
  | v::vs ->
      if aconv tm v then Some index
      else pft_bound_index tm vs (index + 1);;

let rec pft_term_identity_env env tm =
  if is_var tm then
    let name, ty = dest_var tm in
    (match pft_bound_index tm env 0 with
     | Some index -> "b" ^ string_of_int index ^ ";"
     | None -> "v" ^ pft_atom_identity name ^ pft_type_identity ty)
  else if is_const tm then
    let name, ty = dest_const tm in
    "c" ^ pft_atom_identity name ^ pft_type_identity ty
  else if is_comb tm then
    let rator, rand = dest_comb tm in
    "m" ^ pft_term_identity_env env rator ^
    pft_term_identity_env env rand ^ ";"
  else if is_abs tm then
    let var, body = dest_abs tm in
    "l" ^ pft_type_identity (type_of var) ^
    pft_term_identity_env (var::env) body ^ ";"
  else failwith "pft_term_identity: unknown term node";;

let pft_term_identity tm = pft_term_identity_env [] tm;;

(* Exact primitive axioms emitted by HOL's PFTCandlePreamble.  The identity
   format includes constant and free-variable types, and uses de Bruijn
   indices for bound variables so harmless binder renaming is accepted. *)
let pft_standard_axiom_identities =
  [
    ("SELECT_AX",
     "mc1:!t3:fun2[t3:fun2[t3:fun2[v2:'at4:bool0[]]t4:bool0[]]" ^
     "t4:bool0[]]lt3:fun2[v2:'at4:bool0[]]mc1:!t3:fun2[t3:fun2[" ^
     "v2:'at4:bool0[]]t4:bool0[]]lv2:'ammc3:==>t3:fun2[t4:bool0[]" ^
     "t3:fun2[t4:bool0[]t4:bool0[]]]mb1;b0;;;mb1;mc1:@t3:fun2[" ^
     "t3:fun2[v2:'at4:bool0[]]v2:'a]b1;;;;;;;;");
    ("ETA_AX",
     "mc1:!t3:fun2[t3:fun2[t3:fun2[v2:'av2:'b]t4:bool0[]]t4:bool0[]]" ^
     "lt3:fun2[v2:'av2:'b]mmc1:=t3:fun2[t3:fun2[v2:'av2:'b]" ^
     "t3:fun2[t3:fun2[v2:'av2:'b]t4:bool0[]]]lv2:'amb1;b0;;;;b0;;;;");
    ("INFINITY_AX",
     "mc1:?t3:fun2[t3:fun2[t3:fun2[t3:ind0[]t3:ind0[]]t4:bool0[]]" ^
     "t4:bool0[]]lt3:fun2[t3:ind0[]t3:ind0[]]mmc2:/\\t3:fun2[" ^
     "t4:bool0[]t3:fun2[t4:bool0[]t4:bool0[]]]mc7:ONE_ONEt3:fun2[" ^
     "t3:fun2[t3:ind0[]t3:ind0[]]t4:bool0[]]b0;;;mc1:~t3:fun2[" ^
     "t4:bool0[]t4:bool0[]]mc4:ONTOt3:fun2[t3:fun2[t3:ind0[]" ^
     "t3:ind0[]]t4:bool0[]]b0;;;;;;")
  ];;

let allow_standard_pft_axioms () =
  pft_axiom_policy :=
    (fun name tm ->
       try assoc name pft_standard_axiom_identities = pft_term_identity tm
       with Failure _ -> false);;

let allow_pft_axioms_exact allowed =
  pft_axiom_policy :=
    (fun name tm ->
       try aconv (assoc name allowed) tm with Failure _ -> false);;

let pft_theorem_identity th =
  let hypotheses, conclusion = dest_thm th in
  let hypothesis_ids =
    sort (fun left right -> String.compare left right < 0)
         (map pft_term_identity hypotheses) in
  "h" ^ string_of_int (length hypothesis_ids) ^ "[" ^
  pft_concat_identities pft_atom_identity hypothesis_ids ^ "]c" ^
  pft_atom_identity (pft_term_identity conclusion);;

type pft_replay_result =
  | Pft_replay_result of
      string * int * (int * int * int) * (int * int * int) *
      (string * string) list * (string * string) list * bool
;;

let pft_result_trace_path (Pft_replay_result (x,_,_,_,_,_,_)) = x;;
let pft_result_command_count (Pft_replay_result (_,x,_,_,_,_,_)) = x;;
let pft_result_table_limits (Pft_replay_result (_,_,x,_,_,_,_)) = x;;
let pft_result_peak_live (Pft_replay_result (_,_,_,x,_,_,_)) = x;;
let pft_result_saved_theorems (Pft_replay_result (_,_,_,_,x,_,_)) = x;;
let pft_result_axioms (Pft_replay_result (_,_,_,_,_,x,_)) = x;;
let pft_result_compute_initialized
    (Pft_replay_result (_,_,_,_,_,_,x)) = x;;

let decode_uleb128 : Text_io.instream -> int =
  let zero     = Cake.Word8.fromInt   0 in
  let lower7   = Cake.Word8.fromInt 127 in
  let high_bit = Cake.Word8.fromInt 128 in
  let rec decode_uleb128 acc shift byte_count fd =
    if byte_count >= 9 then failwith "decode_uleb128: integer overflow" else
    match Text_io.input1 fd with
    | None -> failwith "decode_uleb128: EOF"
    | Some char ->
       let byte = Cake.Word8.fromChar char in
       let payload = Cake.Word8.toInt (Cake.Word8.andb byte lower7) in
       let _ =
         if payload > (max_int - acc) / shift
         then failwith "decode_uleb128: integer overflow" else () in
       let acc = payload * shift + acc in
       let done_ = Cake.Word8.(=) zero (Cake.Word8.andb byte high_bit) in
       if done_ then
         if byte_count > 0 && payload = 0
         then failwith "decode_uleb128: non-canonical encoding"
         else acc
       else if shift > max_int / 128
       then failwith "decode_uleb128: integer overflow"
       else decode_uleb128 acc (shift * 128) (byte_count + 1) fd
  in decode_uleb128 0 1 0;;

let decode_uleb128_bytes bytes start end_ =
  let lower7 = Cake.Word8.fromInt 127 in
  let high_bit = Cake.Word8.fromInt 128 in
  let zero = Cake.Word8.fromInt 0 in
  let rec loop acc shift byte_count pos =
    if pos >= end_ then failwith "footer: truncated varint"
    else if byte_count >= 9 then failwith "footer: integer overflow"
    else
      let byte = Bytes.get bytes pos in
      let payload = Cake.Word8.toInt (Cake.Word8.andb byte lower7) in
      let _ =
        if payload > (max_int - acc) / shift
        then failwith "footer: integer overflow" else () in
      let acc = payload * shift + acc in
      let done_ = Cake.Word8.(=) zero (Cake.Word8.andb byte high_bit) in
      if done_ then
        if byte_count > 0 && payload = 0
        then failwith "footer: non-canonical varint"
        else (acc, pos + 1)
      else if shift > max_int / 128
      then failwith "footer: integer overflow"
      else loop acc (shift * 128) (byte_count + 1) (pos + 1) in
  loop 0 1 0 start;;

let process_footer trace_path =
  let chunk_size = 32768 in
  let tail_size = 64 in
  let stream = Text_io.openIn trace_path in
  let buffer = Bytes.create chunk_size in
  let tail = ref (Bytes.create tail_size) in
  let tail_len = ref 0 in
  let rec scan () =
    let n = Text_io.input stream buffer 0 chunk_size in
    if n = 0 then ()
    else if n >= tail_size then (
      Cake.Word8_array.copy buffer (n - tail_size) tail_size !tail 0;
      tail_len := tail_size;
      scan ())
    else
      let keep =
        if !tail_len < tail_size - n then !tail_len else tail_size - n in
      let next_tail = Bytes.create tail_size in
      let _ =
        Cake.Word8_array.copy !tail (!tail_len - keep) keep next_tail 0 in
      let _ = Cake.Word8_array.copy buffer 0 n next_tail keep in
      tail := next_tail;
      tail_len := keep + n;
      scan () in
  let _ =
    try scan (); Text_io.closeIn stream
    with e -> Text_io.closeIn stream; raise e in
  if !tail_len < 6 then failwith "footer: file too short" else
  let lo = Cake.Word8.toInt (Bytes.get !tail (!tail_len - 2)) in
  let hi = Cake.Word8.toInt (Bytes.get !tail (!tail_len - 1)) in
  let footer_len = lo + 256 * hi in
  if footer_len < 4 || footer_len + 2 > !tail_len
  then failwith "footer: invalid length" else
  let start = !tail_len - footer_len - 2 in
  if Cake.Word8.toInt (Bytes.get !tail start) <> 0xFF
  then failwith "footer: bad opcode" else
  let n_ty, pos = decode_uleb128_bytes !tail (start + 1) (!tail_len - 2) in
  let n_tm, pos = decode_uleb128_bytes !tail pos (!tail_len - 2) in
  let n_th, pos = decode_uleb128_bytes !tail pos (!tail_len - 2) in
  if pos <> !tail_len - 2 then failwith "footer: unexpected payload"
  else (n_ty, n_tm, n_th);;

let expect_char fd char =
  match Text_io.input1 fd with
  | None -> failwith "expect_char: EOF"
  | Some char' ->
     if char = char' then ()
     else failwith ("expect_char: unexpected " ^ String.make 1 char);;

let expect_pft fd =
  expect_char fd 'P'; expect_char fd 'F'; expect_char fd 'T';
  expect_char fd '\000';;

let read_exactly fd n =
  let bytes = Bytes.create n in
  let rec loop i =
    if i = n then () else
    match Text_io.input1 fd with
    | None -> failwith "read_exactly: EOF"
    | Some c -> Bytes.set bytes i (Cake.Word8.fromChar c); loop (i + 1)
  in
  if n < 0 then failwith ("read_exactly: negative argument")
  else loop 0; Bytes.to_string bytes;;

let valid_pft_utf8 s =
  let len = String.length s in
  let byte i = Char.code (String.get s i) in
  let continuation i =
    i < len && 0x80 <= byte i && byte i <= 0xBF in
  let rec loop i =
    if i >= len then true else
    let b0 = byte i in
    if b0 < 0x20 || b0 = 0x7F then false
    else if b0 <= 0x7E then loop (i + 1)
    else if b0 = 0xC2 then
      i + 1 < len && 0xA0 <= byte (i + 1) && byte (i + 1) <= 0xBF &&
      loop (i + 2)
    else if 0xC3 <= b0 && b0 <= 0xDF then
      continuation (i + 1) && loop (i + 2)
    else if b0 = 0xE0 then
      i + 2 < len && 0xA0 <= byte (i + 1) && byte (i + 1) <= 0xBF &&
      continuation (i + 2) && loop (i + 3)
    else if (0xE1 <= b0 && b0 <= 0xEC) || (0xEE <= b0 && b0 <= 0xEF) then
      continuation (i + 1) && continuation (i + 2) && loop (i + 3)
    else if b0 = 0xED then
      i + 2 < len && 0x80 <= byte (i + 1) && byte (i + 1) <= 0x9F &&
      continuation (i + 2) && loop (i + 3)
    else if b0 = 0xF0 then
      i + 3 < len && 0x90 <= byte (i + 1) && byte (i + 1) <= 0xBF &&
      continuation (i + 2) && continuation (i + 3) && loop (i + 4)
    else if 0xF1 <= b0 && b0 <= 0xF3 then
      continuation (i + 1) && continuation (i + 2) &&
      continuation (i + 3) && loop (i + 4)
    else if b0 = 0xF4 then
      i + 3 < len && 0x80 <= byte (i + 1) && byte (i + 1) <= 0x8F &&
      continuation (i + 2) && continuation (i + 3) && loop (i + 4)
    else false in
  loop 0;;

let decode_string fd =
  let s_len = decode_uleb128 fd in
  if s_len > !pft_max_string_length
  then failwith "decode_string: length exceeds configured limit"
  else let s = read_exactly fd s_len in
    if valid_pft_utf8 s then s
    else failwith "decode_string: invalid UTF-8 or control character";;

let decode_count kind fd =
  let n = decode_uleb128 fd in
  if n > !pft_max_list_length
  then failwith (kind ^ " count exceeds configured limit") else n;;

let next_command fd = Text_io.input1 fd;;

(* --- Replay files --- *)

let replay trace_path =

let _ = print ("Processing " ^ trace_path ^ "\n") in
let _ = print_types_of_subterms := 2 in

let (n_ty, n_tm, n_th) = process_footer trace_path in

let check_table_limit kind n =
  if n < 0 || n > !pft_max_table_slots
  then failwith (kind ^ " table limit exceeds configured maximum") else () in
let _ = check_table_limit "type" n_ty in
let _ = check_table_limit "term" n_tm in
let _ = check_table_limit "theorem" n_th in

let tys = Array.make n_ty (None: hol_type option) in
let tms = Array.make n_tm (None: term option) in
let ths = Array.make n_th (None: thm option) in
let command_stream = Text_io.openIn trace_path in
let live_ty = ref 0 in
let live_tm = ref 0 in
let live_th = ref 0 in
let peak_ty = ref 0 in
let peak_tm = ref 0 in
let peak_th = ref 0 in
let trace_saved = ref ([]: (string * thm) list) in
let trace_axioms = ref ([]: (string * term) list) in

let note_set live peak =
  live := !live + 1;
  if !live > !peak then peak := !live else () in
let note_del live = live := !live - 1 in

let get_ty id =
  if id < 0 || id >= Array.length tys then
    failwith ("type ID out of range: " ^ string_of_int id)
  else match Array.get tys id with
  | Some ty -> ty
  | None -> failwith ("dead type ID: " ^ string_of_int id) in
let get_tm id =
  if id < 0 || id >= Array.length tms then
    failwith ("term ID out of range: " ^ string_of_int id)
  else match Array.get tms id with
  | Some tm -> tm
  | None -> failwith ("dead term ID: " ^ string_of_int id) in
let get_th id =
  if id < 0 || id >= Array.length ths then
    failwith ("theorem ID out of range: " ^ string_of_int id)
  else match Array.get ths id with
  | Some th -> th
  | None -> failwith ("dead theorem ID: " ^ string_of_int id) in

let check_free_ty id =
  if id < 0 || id >= Array.length tys then
    failwith ("type result ID out of range: " ^ string_of_int id)
  else match Array.get tys id with
  | None -> ()
  | Some _ -> failwith ("live type result ID: " ^ string_of_int id) in
let check_free_tm id =
  if id < 0 || id >= Array.length tms then
    failwith ("term result ID out of range: " ^ string_of_int id)
  else match Array.get tms id with
  | None -> ()
  | Some _ -> failwith ("live term result ID: " ^ string_of_int id) in
let check_free_th id =
  if id < 0 || id >= Array.length ths then
    failwith ("theorem result ID out of range: " ^ string_of_int id)
  else match Array.get ths id with
  | None -> ()
  | Some _ -> failwith ("live theorem result ID: " ^ string_of_int id) in

let set_ty id ty =
  check_free_ty id; Array.set tys id (Some ty); note_set live_ty peak_ty in
let set_tm id tm =
  check_free_tm id; Array.set tms id (Some tm); note_set live_tm peak_tm in
let set_th id th =
  check_free_th id; Array.set ths id (Some th); note_set live_th peak_th in

let del_ty id =
  let _ = get_ty id in Array.set tys id None; note_del live_ty in
let del_tm id =
  let _ = get_tm id in Array.set tms id None; note_del live_tm in
let del_th id =
  let _ = get_th id in Array.set ths id None; note_del live_th in
let del_range del lo hi =
  if hi < lo then failwith "DEL range has descending bounds" else
  let rec validate i =
    if i > hi then () else let _ = del i in validate (i + 1) in
  validate lo in

let cmd_cnt = ref 0 in
let incr_cnt () = cmd_cnt := !cmd_cnt + 1 in
let print_cnt () = print (string_of_int (!cmd_cnt) ^ "\n") in

let cleanup () =
  print_cnt (); Text_io.closeIn command_stream in

let pft_tyvar () =
  let id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let result = Kernel.mk_vartype name in
  set_ty id result in

let pft_tyop () =
  let id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let n_args = decode_count "TYOP arguments" command_stream in
  let rec loop i args =
    if i <= 0 then rev args else
      let id = decode_uleb128 command_stream in
      let ty = get_ty id in
      loop (i - 1) (ty::args) in
  let args = loop n_args [] in
  let result = Kernel.mk_type (name, args) in
  set_ty id result in

let pft_const () =
  let id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let type_id = decode_uleb128 command_stream in
  let ty = get_ty type_id in
  let result = mk_mconst (name, ty) in
  set_tm id result in

let pft_var () =
  let id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let type_id = decode_uleb128 command_stream in
  let ty = get_ty type_id in
  let result = Kernel.mk_var (name, ty) in
  set_tm id result in

let pft_abs () =
  let id = decode_uleb128 command_stream in
  let var_id = decode_uleb128 command_stream in
  let body_id = decode_uleb128 command_stream in
  let var_tm = get_tm var_id in
  let body_tm = get_tm body_id in
  let result = Kernel.mk_abs (var_tm, body_tm) in
  set_tm id result in

let pft_comb () =
  let id = decode_uleb128 command_stream in
  let rator_id = decode_uleb128 command_stream in
  let rand_id = decode_uleb128 command_stream in
  let rator_tm = get_tm rator_id in
  let rand_tm = get_tm rand_id in
  let result = mk_comb (rator_tm, rand_tm) in
  set_tm id result in

let pft_assume () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let tm = get_tm tm_id in
  let result = Kernel.ASSUME tm in
  set_th id result in

let pft_new_specification () =
  let id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let n_names = decode_count "new_specification names" command_stream in
  let rec loop i names =
    if i <= 0 then rev names else
      let name = decode_string command_stream in
      loop (i - 1) (name::names) in
  let names = loop n_names [] in
  let th = get_th th_id in
  let actual_names =
    map (fun eq -> fst (dest_var (lhs eq))) (hyp th) in
  let _ =
    if names <> actual_names
    then failwith "new_specification: encoded names do not match witnesses"
    else () in
  let _ = check_free_th id in
  let result = Kernel.new_specification th in
  set_th id result in

let pft_new_type_definition () =
  let id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let tyname = decode_string command_stream in
  let absname = decode_string command_stream in
  let repname = decode_string command_stream in
  let th = get_th th_id in
  let _ = check_free_th id; check_free_th (id + 1) in
  let absth, repth =
    Kernel.new_basic_type_definition (tyname, (absname, (repname, th))) in
  set_th id absth;
  set_th (id + 1) repth in

let pft_compute_init () =
  let n_eqs = decode_count "COMPUTE_INIT equations" command_stream in
  let rec loop i eqs =
    if i <= 0 then rev eqs else
      let eq_id = decode_uleb128 command_stream in
      let eq = get_th eq_id in
      let _ =
        if hyp eq = [] then ()
        else failwith "COMPUTE_INIT: equation has hypotheses" in
      loop (i - 1) (eq::eqs) in
  let eqs = loop n_eqs [] in
  (match !pft_compute_context with
   | None -> pft_compute_context := Some eqs
   | Some _ -> failwith "COMPUTE_INIT: already initialized") in

let pft_compute () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let n_ths = decode_count "COMPUTE equations" command_stream in
  let rec loop i eqs =
    if i <= 0 then rev eqs else
      let eq_id = decode_uleb128 command_stream in
      let eq = get_th eq_id in
      let _ =
        if hyp eq = [] then ()
        else failwith "COMPUTE: code equation has hypotheses" in
      loop (i - 1) (eq::eqs) in
  let eqs = match !pft_compute_context with
    | Some eqs -> eqs
    | None -> failwith "COMPUTE: before COMPUTE_INIT" in
  let code_eqs = loop n_ths [] in
  let tm = get_tm tm_id in
  let th = Kernel.compute (eqs, code_eqs) tm in
  set_th id th in

let pft_save () =
  let name = decode_string command_stream in
  let th_id = decode_uleb128 command_stream in
  let th = get_th th_id in
  save_th name th;
  trace_saved := (name, th)::(!trace_saved) in

let pft_load () =
  let th_id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let th = load_th name !saved_ths in
  set_th th_id th in

let pft_sym () =
  let id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let th = get_th th_id in
  let result = SYM th in
  set_th id result in

let pft_prove_hyp () =
  let id = decode_uleb128 command_stream in
  let th1_id = decode_uleb128 command_stream in
  let th2_id = decode_uleb128 command_stream in
  let th1 = get_th th1_id in
  let th2 = get_th th2_id in
  let result = PROVE_HYP th1 th2 in
  set_th id result in

let pft_refl () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let tm = get_tm tm_id in
  let result = REFL tm in
  set_th id result in

let pft_trans () =
  let id = decode_uleb128 command_stream in
  let th1_id = decode_uleb128 command_stream in
  let th2_id = decode_uleb128 command_stream in
  let th1 = get_th th1_id in
  let th2 = get_th th2_id in
  let result = Kernel.TRANS th1 th2 in
  set_th id result in

let pft_mk_comb_thm () =
  let id = decode_uleb128 command_stream in
  let th1_id = decode_uleb128 command_stream in
  let th2_id = decode_uleb128 command_stream in
  let th1 = get_th th1_id in
  let th2 = get_th th2_id in
  let result = MK_COMB (th1, th2) in
  set_th id result in

let pft_abs_thm () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let tm = get_tm tm_id in
  let th = get_th th_id in
  let result = ABS tm th in
  set_th id result in

let pft_new_const () =
  let name = decode_string command_stream in
  let ty_id = decode_uleb128 command_stream in
  let ty = get_ty ty_id in
  Kernel.new_constant (name, ty) in

let pft_new_type () =
  let name = decode_string command_stream in
  let arity = decode_uleb128 command_stream in
  Kernel.new_type (name, arity) in

let pft_axiom () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let tm = get_tm tm_id in
  let _ = check_free_th id in
  let _ =
    if !pft_axiom_policy name tm then ()
    else failwith ("AXIOM: rejected by policy: " ^ name) in
  let result = Kernel.new_axiom tm in
  let _ = pft_axioms_used := (name, tm)::(!pft_axioms_used) in
  let _ = trace_axioms := (name, tm)::(!trace_axioms) in
  set_th id result in

let pft_beta () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let tm = get_tm tm_id in
  let result = Kernel.BETA tm in
  set_th id result in

let pft_eq_mp () =
  let id = decode_uleb128 command_stream in
  let eq_id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let eq = get_th eq_id in
  let th = get_th th_id in
  let result = EQ_MP eq th in
  set_th id result in

let pft_deduct_antisym_rule () =
  let id = decode_uleb128 command_stream in
  let th1_id = decode_uleb128 command_stream in
  let th2_id = decode_uleb128 command_stream in
  let th1 = get_th th1_id in
  let th2 = get_th th2_id in
  let result = DEDUCT_ANTISYM_RULE th1 th2 in
  set_th id result in

let pft_inst () =
  let id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let n_pairs = decode_count "INST substitutions" command_stream in
  let rec loop i pairs =
    if i <= 0 then rev pairs else
      let id1 = decode_uleb128 command_stream in
      let id2 = decode_uleb128 command_stream in
      let tm1 = get_tm id1 in
      let tm2 = get_tm id2 in
      loop (i - 1) ((tm2, tm1)::pairs) in
  let pairs = loop n_pairs [] in
  let th = get_th th_id in
  let result = Kernel.INST pairs th in
  set_th id result in

let pft_inst_type () =
  let id = decode_uleb128 command_stream in
  let th_id = decode_uleb128 command_stream in
  let n_pairs = decode_count "INST_TYPE substitutions" command_stream in
  let rec loop i pairs =
    if i <= 0 then rev pairs else
      let id1 = decode_uleb128 command_stream in
      let id2 = decode_uleb128 command_stream in
      let ty1 = get_ty id1 in
      let ty2 = get_ty id2 in
      loop (i - 1) ((ty2, ty1)::pairs) in
  let pairs = loop n_pairs [] in
  let th = get_th th_id in
  let result = Kernel.INST_TYPE pairs th in
  set_th id result in

let pft_expect () =
  let id = decode_uleb128 command_stream in
  let th = get_th id in
  let actual_hyps = hyp th in
  let actual_concl = concl th in
  let n_hyps = decode_count "EXPECT hypotheses" command_stream in
  let rec loop i hyps =
    if i <= 0 then rev hyps else
      let hyp_id = decode_uleb128 command_stream in
      let tm = get_tm hyp_id in
      loop (i - 1) (tm::hyps) in
  let expected_hyps = loop n_hyps [] in
  let subset_aconv l1 l2 = forall (fun t1 -> exists (aconv t1) l2) l1 in
  let set_eq_aconv l1 l2 = subset_aconv l1 l2 && subset_aconv l2 l1 in
  if not (set_eq_aconv expected_hyps actual_hyps) then failwith "mismatched hypotheses!";
  let concl_id = decode_uleb128 command_stream in
  let expected_concl = get_tm concl_id in
  if not (aconv expected_concl actual_concl) then failwith "mismatched conclusion!";
  () in

let pft_footer () =
  let footer_n_ty = decode_uleb128 command_stream in
  let footer_n_tm = decode_uleb128 command_stream in
  let footer_n_th = decode_uleb128 command_stream in
  let _ =
    if footer_n_ty <> n_ty || footer_n_tm <> n_tm || footer_n_th <> n_th
    then failwith "footer limits changed between reads" else () in
  let rec encoded_length n =
    if n < 128 then 1 else 1 + encoded_length (n / 128) in
  let expected_length =
    1 + encoded_length n_ty + encoded_length n_tm + encoded_length n_th in
  let lo = match Text_io.input1 command_stream with
    | Some c -> Char.code c
    | None -> failwith "footer: missing length" in
  let hi = match Text_io.input1 command_stream with
    | Some c -> Char.code c
    | None -> failwith "footer: truncated length" in
  let _ =
    if lo + 256 * hi <> expected_length
    then failwith "footer: invalid encoded length" else () in
  match Text_io.input1 command_stream with
  | None -> ()
  | Some _ -> failwith "footer: trailing bytes" in

let seen_footer = ref false in

let rec command_loop () =
  match next_command command_stream with
  | None -> ()
  | Some cmd_char ->
     let cmd = Char.code cmd_char in
     if cmd = 0x01 then pft_tyvar ()
     else if cmd = 0x02 then pft_tyop ()
     else if cmd = 0x03 then pft_var ()
     else if cmd = 0x04 then pft_const ()
     else if cmd = 0x05 then pft_comb ()
     else if cmd = 0x06 then pft_abs ()
     else if cmd = 0x07 then pft_new_const ()
     else if cmd = 0x08 then pft_new_type ()
     else if cmd = 0x09 then pft_axiom ()
     else if cmd = 0x10 then pft_refl ()
     else if cmd = 0x11 then pft_trans ()
     else if cmd = 0x12 then pft_mk_comb_thm ()
     else if cmd = 0x13 then pft_abs_thm ()
     else if cmd = 0x14 then pft_beta ()
     else if cmd = 0x15 then pft_assume ()
     else if cmd = 0x16 then pft_eq_mp ()
     else if cmd = 0x17 then pft_deduct_antisym_rule ()
     else if cmd = 0x18 then pft_inst ()
     else if cmd = 0x19 then pft_inst_type ()
     else if cmd = 0x20 then pft_sym ()
     else if cmd = 0x21 then pft_prove_hyp ()
     else if cmd = 0x30 then pft_new_specification ()
     else if cmd = 0x31 then pft_new_type_definition ()
     else if cmd = 0x40 then pft_compute_init ()
     else if cmd = 0x41 then pft_compute ()
     else if cmd = 0x50 then pft_save ()
     else if cmd = 0x51 then pft_load ()
     else if cmd = 0xE0 then del_ty (decode_uleb128 command_stream)
     else if cmd = 0xE1 then del_tm (decode_uleb128 command_stream)
     else if cmd = 0xE2 then del_th (decode_uleb128 command_stream)
     else if cmd = 0xEF then pft_expect ()
     else if cmd = 0xF0 then
       let lo = decode_uleb128 command_stream in
       let hi = decode_uleb128 command_stream in del_range del_ty lo hi
     else if cmd = 0xF1 then
       let lo = decode_uleb128 command_stream in
       let hi = decode_uleb128 command_stream in del_range del_tm lo hi
     else if cmd = 0xF2 then
       let lo = decode_uleb128 command_stream in
       let hi = decode_uleb128 command_stream in del_range del_th lo hi
     else if cmd = 0xFF then
       if !seen_footer then failwith "duplicate footer"
       else (seen_footer := true; pft_footer ())
     else failwith ("command_loop: unsupported command: " ^ string_of_int cmd);
     incr_cnt ();
     command_loop () in

let _ = expect_pft command_stream in
let version = decode_string command_stream in
let _ =
  if version <> "0.1.0" then failwith ("unsupported version: " ^ version) in
let ruleset = decode_string command_stream in
let _ =
  if ruleset <> "candle" then failwith ("unsupported ruleset: " ^ ruleset) in
let _ = incr_cnt () in

(try command_loop () with e -> (cleanup (); raise e));
let _ = if not !seen_footer then (cleanup (); failwith "missing footer") else () in
let saved_evidence =
  map (fun (name, th) -> (name, pft_theorem_identity th))
      (rev (!trace_saved)) in
let axiom_evidence =
  map (fun (name, tm) -> (name, pft_term_identity tm))
      (rev (!trace_axioms)) in
let result =
  Pft_replay_result
    (trace_path, !cmd_cnt, (n_ty, n_tm, n_th),
     (!peak_ty, !peak_tm, !peak_th), saved_evidence, axiom_evidence,
     (match !pft_compute_context with None -> false | Some _ -> true)) in
cleanup (); print "Success!\n"; result;;

let replay_all paths = map replay paths;;
