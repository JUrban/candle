(* Chunked transport for the canonical V3 kernel state.  Load this after
   candle/fingerprint.ml.  The component item construction is the
   same as the V3 serializer, but the aggregate list and kernel-state strings
   are never concatenated.  A controller can hash the exact wire by joining
   the ordered chunks and reconstructing the length-prefixed kernel node. *)

let candle_v3_stream_chunk_bytes = 8192;;

let candle_v3_stream_field_wire_length length =
  String.length (string_of_int length) + 1 + length;;

let candle_v3_stream_node_header tag count =
  candle_s1_field tag ^ candle_s1_field (string_of_int count);;

let candle_v3_stream_list_header count =
  candle_v3_stream_node_header "list" count;;

let candle_v3_stream_list_wire_length items =
  List.fold_left
    (fun total item ->
      total + candle_v3_stream_field_wire_length (String.length item))
    (String.length (candle_v3_stream_list_header (List.length items)))
    items;;

let candle_v3_stream_kernel_wire_length component_lengths =
  List.fold_left
    (fun total length ->
      total + candle_v3_stream_field_wire_length length)
    (String.length (candle_v3_stream_node_header "kernel-state" 4))
    component_lengths;;

let candle_v3_stream_type_constant_items () =
  List.sort String.compare
    (List.map (fun (name,arity) ->
      candle_s1_node "type-constant-declaration"
        [name; string_of_int arity]) (types()));;

let candle_v3_stream_term_constant_items generated_constants =
  List.sort String.compare
    (List.map (fun (name,ty) ->
      candle_s1_node "term-constant-declaration"
        [candle_s1_canonical_generated "_" "_CANDLE_GENERATED_CONSTANT_"
           generated_constants name;
         candle_s1_type ty]) (constants()));;

let candle_v3_stream_theorem_items generated_constants theorems =
  List.sort String.compare
    (List.map (fun theorem ->
      let identity,_,_ =
        candle_s1_theorem_parts_with_constants generated_constants theorem in
      identity) theorems);;

let rec candle_v3_stream_emit_raw component sequence value offset =
  if offset = String.length value then sequence else
  let remaining = String.length value - offset in
  let count =
    if remaining < candle_v3_stream_chunk_bytes then remaining
    else candle_v3_stream_chunk_bytes in
  let chunk = String.sub value offset count in
  print_endline
    ("CANDLE_STATE_FINGERPRINT_V3_STREAM_CHUNK\t" ^ component ^ "\t" ^
     string_of_int sequence ^ "\t" ^ candle_s1_hex chunk);
  candle_v3_stream_emit_raw component (sequence + 1) value
    (offset + count);;

let candle_v3_stream_emit_list component expected_length items =
  print_endline
    ("CANDLE_STATE_FINGERPRINT_V3_STREAM_COMPONENT_BEGIN\t" ^ component ^
     "\t" ^ string_of_int expected_length);
  let sequence = candle_v3_stream_emit_raw component 0
    (candle_v3_stream_list_header (List.length items)) 0 in
  let rec emit_items sequence = function
      [] -> sequence
    | item::rest ->
        let prefix = string_of_int (String.length item) ^ ":" in
        let next = candle_v3_stream_emit_raw component sequence prefix 0 in
        let next = candle_v3_stream_emit_raw component next item 0 in
        emit_items next rest in
  let chunks = emit_items sequence items in
  print_endline
    ("CANDLE_STATE_FINGERPRINT_V3_STREAM_COMPONENT_END\t" ^ component ^
     "\t" ^ string_of_int expected_length ^ "\t" ^ string_of_int chunks);;

let candle_s1_emit_state_fingerprint_v3_stream () =
  let generated_constants = candle_s1_generated_constant_names () in
  let type_items = candle_v3_stream_type_constant_items ()
  and term_items =
    candle_v3_stream_term_constant_items generated_constants
  and definition_items =
    candle_v3_stream_theorem_items generated_constants (definitions())
  and axiom_items =
    candle_v3_stream_theorem_items generated_constants (axioms()) in
  let type_length = candle_v3_stream_list_wire_length type_items
  and term_length = candle_v3_stream_list_wire_length term_items
  and definition_length = candle_v3_stream_list_wire_length definition_items
  and axiom_length = candle_v3_stream_list_wire_length axiom_items in
  let kernel_length = candle_v3_stream_kernel_wire_length
    [type_length; term_length; definition_length; axiom_length] in
  print_endline
    ("CANDLE_STATE_FINGERPRINT_V3_STREAM_BEGIN\t" ^
     string_of_int kernel_length ^ "\t" ^
     string_of_int type_length ^ "\t" ^
     string_of_int term_length ^ "\t" ^
     string_of_int definition_length ^ "\t" ^
     string_of_int axiom_length ^ "\t" ^
     string_of_int (List.length type_items) ^ "\t" ^
     string_of_int (List.length term_items) ^ "\t" ^
     string_of_int (List.length definition_items) ^ "\t" ^
     string_of_int (List.length axiom_items));
  candle_v3_stream_emit_list "type_constants" type_length type_items;
  candle_v3_stream_emit_list "term_constants" term_length term_items;
  candle_v3_stream_emit_list "definitions" definition_length definition_items;
  candle_v3_stream_emit_list "global_axioms" axiom_length axiom_items;
  print_endline "CANDLE_STATE_FINGERPRINT_V3_STREAM_END";;
