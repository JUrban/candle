#use "candle/build/insulate.ml";;
#use "candle/nums.ml";;
#use "candle/pretty.ml";;
#use "candle/ocaml.ml";;

let digest_vectors =
  [("empty", "");
   ("a", "a");
   ("abc", "abc");
   ("message", "message digest");
   ("binary", "\000\255\001\254");
   ("pad55", String.make 55 'a');
   ("pad56", String.make 56 'a');
   ("block64", String.make 64 'a');
   ("block65", String.make 65 'a');
   ("thousand", String.make 1000 'a')];;

List.iter
  (fun (label, source) ->
    print_endline
      ("DIGEST:" ^ label ^ "=" ^ Digest.to_hex (Digest.string source)))
  digest_vectors;;

let digest_pattern length =
  let rec build index result =
    if index < 0 then String.concat "" result
    else
      build (index - 1)
        (String.make 1 (Char.chr ((index * 73 + length * 19) mod 256)) :: result) in
  build (length - 1) [];;

let rec emit_digest_lengths length =
  if length > 130 then ()
  else
    (print_endline
       ("DIGEST:len" ^ string_of_int length ^ "=" ^
        Digest.to_hex (Digest.string (digest_pattern length)));
     emit_digest_lengths (length + 1));;
emit_digest_lengths 0;;

print_endline
  ("DIGEST:file=" ^
   Digest.to_hex (Digest.file "candle/flyspeck_metadata/date.txt"));;

let digest_rejects_short =
  try let _ = Digest.to_hex "short" in false
  with Invalid_argument _ -> true;;
print_endline
  ("DIGEST:reject_short=" ^
   (if digest_rejects_short then "true" else "false"));;

print_endline "CANDLE_DIGEST_COMPAT_OK";;
