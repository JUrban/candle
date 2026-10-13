(* ========================================================================== *)
(* Export the exact checked equation/call identity for the cell-0 fast gate.  *)
(*                                                                            *)
(* The serializer is deliberately streaming and uses an explicit work list:  *)
(* genuine raw certificate cval lists are deep enough that building one       *)
(* recursively concatenated source string is both quadratic and stack-heavy. *)
(* ========================================================================== *)

module Benchmark_cv_compute_analytic_expr_case10173_registered_cell0_export = struct

open Benchmark_cv_compute_analytic_expr_case10173_registered_cell0_capture;;

let candle_registered_cell0_export_path =
  "/project/flyspeck-candle-runs/nl-case10173-registered-cell0-generated-v1.sml";;

let candle_registered_cell0_mlstring name =
  "«" ^ name ^ "»";;

type candle_registered_cell0_write_task =
  | Candle_registered_cell0_text of string
  | Candle_registered_cell0_exp of term
  | Candle_registered_cell0_cv of term;;

let rec candle_registered_cell0_argument_tasks arguments =
  match arguments with
  | [] -> [Candle_registered_cell0_text "]"]
  | [argument] ->
      [Candle_registered_cell0_exp argument;
       Candle_registered_cell0_text "]"]
  | argument :: remaining ->
      Candle_registered_cell0_exp argument ::
      Candle_registered_cell0_text ";" ::
      candle_registered_cell0_argument_tasks remaining;;

let rec candle_registered_cell0_write_tasks channel tasks =
  match tasks with
  | [] -> ()
  | Candle_registered_cell0_text text :: remaining ->
      output_string channel text;
      candle_registered_cell0_write_tasks channel remaining
  | Candle_registered_cell0_cv term :: remaining ->
      let operator,args = strip_comb term in
      let name,_ = dest_const operator in
      (match name,args with
       | "Cexp_num",[numeral] ->
           output_string channel
             ("Num " ^ Num.string_of_num (dest_numeral numeral));
           candle_registered_cell0_write_tasks channel remaining
       | "Cexp_pair",[left;right] ->
           output_string channel "Pair (";
           candle_registered_cell0_write_tasks channel
             (Candle_registered_cell0_cv left ::
              Candle_registered_cell0_text ") (" ::
              Candle_registered_cell0_cv right ::
              Candle_registered_cell0_text ")" :: remaining)
       | _ -> failwith "registered cell0 export: result is not a closed cval")
  | Candle_registered_cell0_exp term :: remaining ->
      (match term with
       | Var (name,_) ->
           output_string channel
             ("Var " ^ candle_registered_cell0_mlstring name);
           candle_registered_cell0_write_tasks channel remaining
       | _ ->
           let operator,args = strip_comb term in
           let name,_ = dest_const operator in
           if name = "LET" then
             (match args with
              | [Abs (Var (bound,_),body);argument] ->
                  output_string channel
                    ("Let " ^ candle_registered_cell0_mlstring bound ^ " (");
                  candle_registered_cell0_write_tasks channel
                    (Candle_registered_cell0_exp argument ::
                     Candle_registered_cell0_text ") (" ::
                     Candle_registered_cell0_exp body ::
                     Candle_registered_cell0_text ")" :: remaining)
              | _ -> failwith "registered cell0 export: malformed LET")
           else if name = "Cexp_num" then
             (match args with
              | [numeral] ->
                  output_string channel
                    ("Num " ^ Num.string_of_num (dest_numeral numeral));
                  candle_registered_cell0_write_tasks channel remaining
              | _ -> failwith "registered cell0 export: malformed Cexp_num")
           else
             match name,args with
             | "Cexp_pair",[left;right] ->
                 output_string channel "Pair (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_fst",[argument] ->
                 output_string channel "Uop Fst (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp argument ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_snd",[argument] ->
                 output_string channel "Uop Snd (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp argument ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_ispair",[argument] ->
                 output_string channel "Uop Ispair (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp argument ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_add",[left;right] ->
                 output_string channel "Binop Add (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_sub",[left;right] ->
                 output_string channel "Binop Sub (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_mul",[left;right] ->
                 output_string channel "Binop Mul (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_div",[left;right] ->
                 output_string channel "Binop Div (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_mod",[left;right] ->
                 output_string channel "Binop Mod (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_less",[left;right] ->
                 output_string channel "Binop Less (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_eq",[left;right] ->
                 output_string channel "Binop Eq (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp left ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp right ::
                    Candle_registered_cell0_text ")" :: remaining)
             | "Cexp_if",[guard;then_branch;else_branch] ->
                 output_string channel "If (";
                 candle_registered_cell0_write_tasks channel
                   (Candle_registered_cell0_exp guard ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp then_branch ::
                    Candle_registered_cell0_text ") (" ::
                    Candle_registered_cell0_exp else_branch ::
                    Candle_registered_cell0_text ")" :: remaining)
             | _,_ ->
                 output_string channel
                   ("App " ^ candle_registered_cell0_mlstring name ^ " [");
                 candle_registered_cell0_write_tasks channel
                   (candle_registered_cell0_argument_tasks args @ remaining));;

let candle_registered_cell0_write_mlstrings channel names =
  let rec write first remaining =
    match remaining with
    | [] -> ()
    | name :: rest ->
        if not first then output_string channel ";";
        output_string channel (candle_registered_cell0_mlstring name);
        write false rest in
  write true names;;

let candle_registered_cell0_write_equation channel theorem =
  let specialized = SPEC_ALL theorem in
  if hyp specialized <> [] then
    failwith "registered cell0 export: equation has hypotheses";
  let lhs,rhs = dest_eq (concl specialized) in
  let operator,args = strip_comb lhs in
  let name,_ = dest_const operator in
  let argument_names = map (fun argument -> fst (dest_var argument)) args in
  output_string channel
    ("(" ^ candle_registered_cell0_mlstring name ^ ",([");
  candle_registered_cell0_write_mlstrings channel argument_names;
  output_string channel "],(";
  candle_registered_cell0_write_tasks channel
    [Candle_registered_cell0_exp rhs];
  output_string channel ")))";;

let _ =
  let captured = candle_case10173_registered_cell0_capture () in
  let channel = open_out candle_registered_cell0_export_path in
  output_string channel
    ("(* Mechanically exported from the exact genuine case-10173 cell-0 " ^
     "complete-wrapper call. *)\n" ^
     "Theory compute_registeredCase10173Cell0Data\n" ^
     "Ancestors compute\n" ^
     "Libs bossLib preamble\n\n" ^
     "Definition registered_case10173_cell0_ceqs_def:\n" ^
     "  registered_case10173_cell0_ceqs :\n" ^
     "    (mlstring # (mlstring list # compute_exp)) list =\n" ^
     "    [");
  let rec write_equations first equations =
    match equations with
    | [] -> ()
    | equation :: remaining ->
        if not first then output_string channel ";\n     ";
        candle_registered_cell0_write_equation channel equation;
        write_equations false remaining in
  write_equations true captured.case10173_registered_cell0_equations;
  output_string channel
    ("]\nEnd\n\n" ^
     "Definition registered_case10173_cell0_cexp_def:\n" ^
     "  registered_case10173_cell0_cexp : compute_exp =\n    ");
  candle_registered_cell0_write_tasks channel
    [Candle_registered_cell0_exp captured.case10173_registered_cell0_call];
  output_string channel
    ("\nEnd\n\n" ^
     "Definition registered_case10173_cell0_result_def:\n" ^
     "  registered_case10173_cell0_result : cv =\n    ");
  candle_registered_cell0_write_tasks channel
    [Candle_registered_cell0_cv
       (rand (concl captured.case10173_registered_cell0_theorem))];
  output_string channel "\nEnd\n\nval _ = export_theory ();\n";
  close_out channel;
  print_endline
    ("CANDLE_CV_CASE10173_REGISTERED_CELL0_EXPORT_OK" ^
     " DEVELOPMENT_NON_RELEASE equations=" ^
     string_of_int (length captured.case10173_registered_cell0_equations) ^
     " path=" ^ candle_registered_cell0_export_path);;

end;;
