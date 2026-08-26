needs "candle/pft/pft.ml";;

let saved_ths = ref ([]: (string * thm) list);;
let save_th name th = saved_ths := (name, th)::(!saved_ths);;
let load_th name = assoc name (!saved_ths);;
let print_saved () =
  do_list (fun (s, th) ->
      print_endline (s ^ ": ");
      Pretty.print_stdout pp_print_colored_thm th;
      print_newline ()
    ) !saved_ths;;

let pft_max_string_length = ref (1024 * 1024);;
let pft_max_table_slots = ref 50000000;;

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

let decode_string fd =
  let s_len = decode_uleb128 fd in
  if s_len > !pft_max_string_length
  then failwith "decode_string: length exceeds configured limit"
  else read_exactly fd s_len;;

let next_command fd = Text_io.input1 fd;;

(* --- Replay files --- *)

let replay trace_path =

let _ = print ("Processing " ^ trace_path ^ "\n") in
let command_stream = Text_io.openIn trace_path in
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
let compute_context = ref (None: thm list option) in

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

let set_ty id ty = check_free_ty id; Array.set tys id (Some ty) in
let set_tm id tm = check_free_tm id; Array.set tms id (Some tm) in
let set_th id th = check_free_th id; Array.set ths id (Some th) in

let del_ty id = let _ = get_ty id in Array.set tys id None in
let del_tm id = let _ = get_tm id in Array.set tms id None in
let del_th id = let _ = get_th id in Array.set ths id None in
let del_range del lo hi =
  if hi < lo then failwith "DEL range has descending bounds" else
  let rec validate i =
    if i > hi then () else let _ = del i in validate (i + 1) in
  validate lo in

let cmd_cnt = ref 1 in
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
  let n_args = decode_uleb128 command_stream in
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
  let n_names = decode_uleb128 command_stream in
  let rec loop i names =
    if i <= 0 then rev names else
      let name = decode_string command_stream in
      loop (i - 1) (name::names) in
  let names = loop n_names [] in
  let th = get_th th_id in
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
  let n_eqs = decode_uleb128 command_stream in
  let rec loop i eqs =
    if i <= 0 then rev eqs else
      let eq_id = decode_uleb128 command_stream in
      let eq = get_th eq_id in
      loop (i - 1) (eq::eqs) in
  let eqs = loop n_eqs [] in
  (match !compute_context with
   | None -> compute_context := Some eqs
   | Some _ -> failwith "COMPUTE_INIT: already initialized") in

let pft_compute () =
  let id = decode_uleb128 command_stream in
  let tm_id = decode_uleb128 command_stream in
  let n_ths = decode_uleb128 command_stream in
  let rec loop i eqs =
    if i <= 0 then rev eqs else
      let eq_id = decode_uleb128 command_stream in
      let eq = get_th eq_id in
      loop (i - 1) (eq::eqs) in
  let eqs = match !compute_context with
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
  save_th name th in

let pft_load () =
  let th_id = decode_uleb128 command_stream in
  let name = decode_string command_stream in
  let th = load_th name in
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
  let result = Kernel.new_axiom tm in
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
  let n_pairs = decode_uleb128 command_stream in
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
  let n_pairs = decode_uleb128 command_stream in
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
  let n_hyps = decode_uleb128 command_stream in
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
cleanup (); print "Success!\n";;

let replay_all paths = List.iter replay paths;;
