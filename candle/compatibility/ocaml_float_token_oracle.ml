(* Independent OCaml 4.14.1 lexer oracle for the Flyspeck float corpus.

   The Python corpus scanner is deliberately not involved.  OCaml's own
   compiler lexer handles comments, strings, character literals, identifiers,
   numeric syntax, and source locations.  When that lexer returns BACKQUOTE in
   code, this helper advances the same lexbuf to the paired closing backtick:
   quotation bodies contain HOL operators that are not OCaml tokens.  Floats
   in those term-language bodies are omitted.  A phrase terminator inside a
   paired span is rejected as ambiguous with two OCaml polymorphic variants. *)

let fail key lexbuf message =
  let position = Lexing.lexeme_start_p lexbuf in
  Printf.eprintf "%s:%d:%d: %s\n"
    key position.pos_lnum
    (position.pos_cnum - position.pos_bol + 1) message;
  exit 2
;;

let skip_hol_quotation key (lexbuf : Lexing.lexbuf) =
  let previous_semicolon = ref false in
  let rec skip () =
    if lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len then
      fail key lexbuf "unterminated HOL backtick quotation"
    else
      let character = Bytes.get lexbuf.lex_buffer lexbuf.lex_curr_pos in
      let position = lexbuf.lex_curr_p in
      lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos + 1;
      lexbuf.lex_curr_p <-
        if character = '\n' then
          {position with
           pos_lnum = position.pos_lnum + 1;
           pos_bol = position.pos_cnum + 1;
           pos_cnum = position.pos_cnum + 1}
        else
          {position with pos_cnum = position.pos_cnum + 1};
      if character <> '`' then begin
        if character = ';' && !previous_semicolon then
          fail key lexbuf
            "ambiguous paired backticks contain an OCaml phrase terminator";
        previous_semicolon := character = ';';
        skip ()
      end
  in
  skip ()
;;

let is_decimal_digit_or_separator = function
  | '0'..'9' | '_' -> true
  | _ -> false
;;

let has_decimal_exponent_prefix literal =
  let rec digits index =
    if index >= String.length literal then false
    else if is_decimal_digit_or_separator literal.[index] then
      digits (index + 1)
    else
      literal.[index] = 'e' || literal.[index] = 'E'
  in
  digits 0
;;

let has_hex_exponent literal =
  String.length literal >= 2 && literal.[0] = '0' &&
  (literal.[1] = 'x' || literal.[1] = 'X') &&
  (String.contains literal 'p' || String.contains literal 'P')
;;

let could_be_float_literal literal =
  String.contains literal '.' ||
  has_decimal_exponent_prefix literal ||
  has_hex_exponent literal
;;

let ensure_progress key (lexbuf : Lexing.lexbuf) previous_position =
  if lexbuf.lex_curr_pos = previous_position then
    if lexbuf.lex_curr_pos >= lexbuf.lex_buffer_len then
      fail key lexbuf "OCaml lexer error without recoverable input"
    else
      let position = lexbuf.lex_curr_p in
      let character = Bytes.get lexbuf.lex_buffer lexbuf.lex_curr_pos in
      lexbuf.lex_curr_pos <- lexbuf.lex_curr_pos + 1;
      lexbuf.lex_curr_p <-
        if character = '\n' then
          {position with
           pos_lnum = position.pos_lnum + 1;
           pos_bol = position.pos_cnum + 1;
           pos_cnum = position.pos_cnum + 1}
        else
          {position with pos_cnum = position.pos_cnum + 1}
;;

let scan key path =
  let channel = open_in_bin path in
  let contents = really_input_string channel (in_channel_length channel) in
  close_in channel;
  let lexbuf = Lexing.from_string contents in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = path};
  Lexer.init ();
  let rec loop () =
    let previous_position = lexbuf.lex_curr_pos in
    let token =
      try Some (Lexer.token lexbuf) with
      | Lexer.Error (Lexer.Invalid_literal literal, _) ->
          if could_be_float_literal literal then
            fail key lexbuf
              ("malformed or suffixed potential float literal: " ^ literal)
          else begin
            ensure_progress key lexbuf previous_position;
            None
          end
      | Lexer.Error (Lexer.Illegal_character _, _) ->
          ensure_progress key lexbuf previous_position;
          None
      | Lexer.Error (_, location) ->
          Printf.eprintf "%s:%d:%d: OCaml lexer error\n"
            key location.loc_start.pos_lnum
            (location.loc_start.pos_cnum - location.loc_start.pos_bol + 1);
          exit 2
    in
    match token with
    | None -> loop ()
    | Some Parser.EOF -> ()
    | Some Parser.BACKQUOTE ->
        skip_hol_quotation key lexbuf;
        loop ()
    | Some (Parser.FLOAT (_, Some suffix)) ->
        fail key lexbuf
          (Printf.sprintf "float suffix %C is outside the Candle grammar" suffix)
    | Some (Parser.FLOAT (_, None)) ->
        let position = Lexing.lexeme_start_p lexbuf in
        Printf.printf "%s\t%d\t%d\t%s\n"
          key position.pos_lnum
          (position.pos_cnum - position.pos_bol + 1)
          (Lexing.lexeme lexbuf);
        loop ()
    | Some _ -> loop ()
  in
  loop ();
;;

let split_input line =
  match String.index_opt line '\t' with
  | None -> invalid_arg "expected key<TAB>path"
  | Some index ->
      let key = String.sub line 0 index in
      let path = String.sub line (index + 1) (String.length line - index - 1) in
      if key = "" || path = "" || String.contains path '\t' then
        invalid_arg "invalid key/path input"
      else
        key, path
;;

let () =
  try
    while true do
      let key, path = split_input (input_line stdin) in
      scan key path
    done
  with End_of_file -> ()
;;
