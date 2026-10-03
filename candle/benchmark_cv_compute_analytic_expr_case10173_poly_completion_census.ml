(* ========================================================================== *)
(* Conservative completion-liveness census for the genuine case-10173       *)
(* polynomial blocks.                                                        *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE / NON-AUTHORITATIVE.  This inspects the exact   *)
(* authenticated reflected source program already held by the complete       *)
(* capture checkpoint.  It performs no proof-authorizing computation.         *)
(* ========================================================================== *)

needs "candle/benchmark_cv_compute_analytic_expr_case10173_complete_capture.ml";;

module Benchmark_cv_compute_analytic_expr_case10173_poly_completion_census = struct

open Candle_cv_analytic_expr_jet_prove;;
open Candle_cv_analytic_expr_stable_program_data;;
open Benchmark_cv_compute_analytic_expr_case10173_complete_capture;;

type candle_case10173_poly_census_node = {
  candle_case10173_poly_census_class : string;
  mutable candle_case10173_poly_census_full_needed : bool;
};;

let candle_case10173_poly_census_pair context tm =
  candle_q_dim_stable_program_dest_cval_pair context tm;;

let candle_case10173_poly_census_num context tm =
  let operator,arguments = strip_comb tm in
  if not (aconv operator `Cexp_num`) then
    failwith ("case10173 polynomial census: expected numeral in " ^ context);
  match arguments with
  | [value] -> dest_small_numeral value
  | _ -> failwith ("case10173 polynomial census: malformed numeral in " ^
                   context);;

let rec candle_case10173_poly_census_list context tm =
  let operator,_ = strip_comb tm in
  if aconv operator `Cexp_num` then []
  else
    let head,tail = candle_case10173_poly_census_pair context tm in
    head :: candle_case10173_poly_census_list context tail;;

let candle_case10173_poly_census_pop context = function
  | head :: tail -> head,tail
  | [] -> failwith ("case10173 polynomial census: stack underflow in " ^
                    context);;

let candle_case10173_poly_census_run_block all_nodes payload =
  let instructions =
    candle_case10173_poly_census_list "polynomial program" payload in
  let rec run stack = function
    | [] ->
        (match stack with
         | [root] ->
             root.candle_case10173_poly_census_full_needed <- true;
             length instructions
         | _ -> failwith "case10173 polynomial census: final stack shape")
    | instruction :: remaining ->
        let operator,_ = strip_comb instruction in
        if aconv operator `Cexp_pair` then
          let tag,_ =
            candle_case10173_poly_census_pair "polynomial leaf" instruction in
          let tag_number =
            candle_case10173_poly_census_num "polynomial leaf tag" tag in
          let node = {
            candle_case10173_poly_census_class =
              if tag_number = 0 then "constant" else "variable";
            candle_case10173_poly_census_full_needed = false;
          } in
          all_nodes := node :: !all_nodes;
          run (node :: stack) remaining
        else
          let opcode =
            candle_case10173_poly_census_num
              "polynomial opcode" instruction in
          if opcode = 2 then
            let _,tail = candle_case10173_poly_census_pop "negation" stack in
            let node = {
              candle_case10173_poly_census_class = "negation";
              candle_case10173_poly_census_full_needed = false;
            } in
            all_nodes := node :: !all_nodes;
            run (node :: tail) remaining
          else if opcode = 3 || opcode = 4 then
            let right,tail_1 =
              candle_case10173_poly_census_pop "binary right" stack in
            let left,tail_2 =
              candle_case10173_poly_census_pop "binary left" tail_1 in
            if opcode = 4 then begin
              left.candle_case10173_poly_census_full_needed <- true;
              right.candle_case10173_poly_census_full_needed <- true
            end;
            let node = {
              candle_case10173_poly_census_class =
                if opcode = 3 then "addition" else "multiplication";
              candle_case10173_poly_census_full_needed = false;
            } in
            all_nodes := node :: !all_nodes;
            run (node :: tail_2) remaining
          else if opcode = 5 then
            let child,tail =
              candle_case10173_poly_census_pop "square" stack in
            child.candle_case10173_poly_census_full_needed <- true;
            let node = {
              candle_case10173_poly_census_class = "square";
              candle_case10173_poly_census_full_needed = false;
            } in
            all_nodes := node :: !all_nodes;
            run (node :: tail) remaining
          else
            failwith
              ("case10173 polynomial census: unexpected opcode " ^
               string_of_int opcode) in
  run [] instructions;;

let candle_case10173_poly_census_count predicate nodes =
  List.fold_left (fun count node -> if predicate node then count + 1 else count)
    0 nodes;;

let candle_case10173_poly_census_class_count name nodes =
  candle_case10173_poly_census_count
    (fun node -> node.candle_case10173_poly_census_class = name) nodes;;

let _ =
  let axioms_before = axioms () in
  let captured = candle_case10173_complete_capture () in
  let source_program =
    captured.case10173_complete_prepared.program_representation_term in
  let top_instructions =
    candle_case10173_poly_census_list "source program" source_program in
  let all_nodes = ref [] in
  let block_count = ref 0 and instruction_count = ref 0 in
  List.iter
    (fun instruction ->
      let operator,_ = strip_comb instruction in
      if aconv operator `Cexp_pair` then
        let tag,payload =
          candle_case10173_poly_census_pair
            "top-level polynomial instruction" instruction in
        if candle_case10173_poly_census_num
             "top-level instruction tag" tag = 0 then begin
          block_count := !block_count + 1;
          instruction_count := !instruction_count +
            candle_case10173_poly_census_run_block all_nodes payload
        end)
    top_instructions;
  let nodes = !all_nodes in
  let full_needed =
    candle_case10173_poly_census_count
      (fun node -> node.candle_case10173_poly_census_full_needed) nodes in
  let completion_dead = length nodes - full_needed in
  let axioms_after = axioms () in
  if length top_instructions <> 54 || !block_count <> 22 ||
     length nodes <> !instruction_count ||
     length axioms_after <> length axioms_before ||
     not (List.for_all (fun axiom -> List.mem axiom axioms_before) axioms_after)
  then failwith "case10173 polynomial census: final validation failed";
  print_endline
    ("CANDLE_CV_CASE10173_POLY_COMPLETION_CENSUS_OK" ^
     " DEVELOPMENT_NON_RELEASE NON_AUTHORITATIVE" ^
     " top_instructions=" ^ string_of_int (length top_instructions) ^
     " blocks=" ^ string_of_int !block_count ^
     " poly_instructions=" ^ string_of_int (length nodes) ^
     " constants=" ^
       string_of_int (candle_case10173_poly_census_class_count "constant" nodes) ^
     " variables=" ^
       string_of_int (candle_case10173_poly_census_class_count "variable" nodes) ^
     " negations=" ^
       string_of_int (candle_case10173_poly_census_class_count "negation" nodes) ^
     " additions=" ^
       string_of_int (candle_case10173_poly_census_class_count "addition" nodes) ^
     " multiplications=" ^
       string_of_int
         (candle_case10173_poly_census_class_count "multiplication" nodes) ^
     " squares=" ^
       string_of_int (candle_case10173_poly_census_class_count "square" nodes) ^
     " completion_live=" ^ string_of_int full_needed ^
     " completion_dead=" ^ string_of_int completion_dead ^
     " assumptions=0 axiom_growth=0");;

end;;
