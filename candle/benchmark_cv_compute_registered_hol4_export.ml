(* ========================================================================== *)
(* Shared streaming exporter for exact Candle compute calls into HOL4 data.  *)
(*                                                                            *)
(* Deep certificate lists must not be rendered by recursive string           *)
(* concatenation.  This module writes an explicit task stack directly to the *)
(* output channel and also computes the reachable equation slice.             *)
(* ========================================================================== *)

module Benchmark_cv_compute_registered_hol4_export = struct

let candle_registered_equation_head theorem =
  let lhs,_ = dest_eq (concl (SPEC_ALL theorem)) in
  let operator,_ = strip_comb lhs in
  fst (dest_const operator);;

let candle_registered_term_constant_names term =
  rev
    (itlist
      (fun constant names ->
        let name,_ = dest_const constant in
        if List.mem name names then names else name :: names)
      (find_terms is_const term) []);;

let candle_registered_equation_slice equations term =
  let named =
    map
      (fun theorem ->
        let specialized = SPEC_ALL theorem in
        let _,rhs = dest_eq (concl specialized) in
        candle_registered_equation_head specialized,theorem,rhs)
      equations in
  let names = map (fun (name,_,_) -> name) named in
  let rec dependencies result = function
    | [] -> rev result
    | name :: remaining ->
        if List.mem name names && not (List.mem name result) then
          dependencies (name :: result) remaining
        else dependencies result remaining in
  let equation_dependencies name =
    let rec collect result = function
      | [] -> result
      | (candidate,_,rhs) :: remaining ->
          let result' =
            if candidate = name then
              itlist
                (fun dependency selected ->
                  if List.mem dependency names &&
                     not (List.mem dependency selected)
                  then dependency :: selected
                  else selected)
                (candle_registered_term_constant_names rhs) result
            else result in
          collect result' remaining in
    collect [] named in
  let rec close pending selected =
    match pending with
    | [] -> selected
    | name :: remaining ->
        if List.mem name selected then close remaining selected
        else if List.mem name names then
          close (equation_dependencies name @ remaining) (name :: selected)
        else close remaining selected in
  let roots = dependencies [] (candle_registered_term_constant_names term) in
  let selected_names = close roots [] in
  List.filter
    (fun theorem ->
      List.mem (candle_registered_equation_head theorem) selected_names)
    equations;;

let candle_registered_mlstring name =
  "«" ^ name ^ "»";;

type candle_registered_write_task =
  | Candle_registered_text of string
  | Candle_registered_exp of term
  | Candle_registered_cv of term;;

let rec candle_registered_argument_tasks arguments =
  match arguments with
  | [] -> [Candle_registered_text "]"]
  | [argument] ->
      [Candle_registered_exp argument; Candle_registered_text "]"]
  | argument :: remaining ->
      Candle_registered_exp argument :: Candle_registered_text ";" ::
      candle_registered_argument_tasks remaining;;

let rec candle_registered_write_tasks channel tasks =
  match tasks with
  | [] -> ()
  | Candle_registered_text text :: remaining ->
      output_string channel text;
      candle_registered_write_tasks channel remaining
  | Candle_registered_cv term :: remaining ->
      let operator,args = strip_comb term in
      let name,_ = dest_const operator in
      (match name,args with
       | "Cexp_num",[numeral] ->
           output_string channel
             ("Num " ^ Num.string_of_num (dest_numeral numeral));
           candle_registered_write_tasks channel remaining
       | "Cexp_pair",[left;right] ->
           output_string channel "Pair (";
           candle_registered_write_tasks channel
             (Candle_registered_cv left :: Candle_registered_text ") (" ::
              Candle_registered_cv right :: Candle_registered_text ")" ::
              remaining)
       | _ -> failwith "registered export: result is not a closed cval")
  | Candle_registered_exp term :: remaining ->
      (match term with
       | Var (name,_) ->
           output_string channel ("Var " ^ candle_registered_mlstring name);
           candle_registered_write_tasks channel remaining
       | _ ->
           let operator,args = strip_comb term in
           let name,_ = dest_const operator in
           if name = "LET" then
             (match args with
              | [Abs (Var (bound,_),body);argument] ->
                  output_string channel
                    ("Let " ^ candle_registered_mlstring bound ^ " (");
                  candle_registered_write_tasks channel
                    (Candle_registered_exp argument ::
                     Candle_registered_text ") (" ::
                     Candle_registered_exp body ::
                     Candle_registered_text ")" :: remaining)
              | _ -> failwith "registered export: malformed LET")
           else if name = "Cexp_num" then
             (match args with
              | [numeral] ->
                  output_string channel
                    ("Num " ^ Num.string_of_num (dest_numeral numeral));
                  candle_registered_write_tasks channel remaining
              | _ -> failwith "registered export: malformed Cexp_num")
           else
             match name,args with
             | "Cexp_pair",[left;right] ->
                 output_string channel "Pair (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_fst",[argument] ->
                 output_string channel "Uop Fst (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp argument ::
                    Candle_registered_text ")" :: remaining)
             | "Cexp_snd",[argument] ->
                 output_string channel "Uop Snd (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp argument ::
                    Candle_registered_text ")" :: remaining)
             | "Cexp_ispair",[argument] ->
                 output_string channel "Uop Ispair (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp argument ::
                    Candle_registered_text ")" :: remaining)
             | "Cexp_add",[left;right] ->
                 output_string channel "Binop Add (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_sub",[left;right] ->
                 output_string channel "Binop Sub (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_mul",[left;right] ->
                 output_string channel "Binop Mul (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_div",[left;right] ->
                 output_string channel "Binop Div (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_mod",[left;right] ->
                 output_string channel "Binop Mod (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_less",[left;right] ->
                 output_string channel "Binop Less (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_eq",[left;right] ->
                 output_string channel "Binop Eq (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp left :: Candle_registered_text ") (" ::
                    Candle_registered_exp right :: Candle_registered_text ")" ::
                    remaining)
             | "Cexp_if",[guard;then_branch;else_branch] ->
                 output_string channel "If (";
                 candle_registered_write_tasks channel
                   (Candle_registered_exp guard :: Candle_registered_text ") (" ::
                    Candle_registered_exp then_branch ::
                    Candle_registered_text ") (" ::
                    Candle_registered_exp else_branch ::
                    Candle_registered_text ")" :: remaining)
             | _,_ ->
                 output_string channel
                   ("App " ^ candle_registered_mlstring name ^ " [");
                 candle_registered_write_tasks channel
                   (candle_registered_argument_tasks args @ remaining));;

let candle_registered_write_mlstrings channel names =
  let rec write first remaining =
    match remaining with
    | [] -> ()
    | name :: rest ->
        if not first then output_string channel ";";
        output_string channel (candle_registered_mlstring name);
        write false rest in
  write true names;;

let candle_registered_write_equation channel theorem =
  let specialized = SPEC_ALL theorem in
  if hyp specialized <> [] then
    failwith "registered export: equation has hypotheses";
  let lhs,rhs = dest_eq (concl specialized) in
  let operator,args = strip_comb lhs in
  let name,_ = dest_const operator in
  let argument_names = map (fun argument -> fst (dest_var argument)) args in
  output_string channel ("(" ^ candle_registered_mlstring name ^ ",([");
  candle_registered_write_mlstrings channel argument_names;
  output_string channel "],(";
  candle_registered_write_tasks channel [Candle_registered_exp rhs];
  output_string channel ")))";;

let candle_registered_write_data_theory channel
      comment theory_name ceqs_name cexp_name result_name equations call result =
  output_string channel
    ("(* " ^ comment ^ " *)\n" ^
     "Theory " ^ theory_name ^ "\n" ^
     "Ancestors compute\n" ^
     "Libs bossLib preamble\n\n" ^
     "Definition " ^ ceqs_name ^ "_def:\n" ^
     "  " ^ ceqs_name ^ " :\n" ^
     "    (mlstring # (mlstring list # compute_exp)) list =\n" ^
     "    [");
  let rec write_equations first remaining =
    match remaining with
    | [] -> ()
    | equation :: rest ->
        if not first then output_string channel ";\n     ";
        candle_registered_write_equation channel equation;
        write_equations false rest in
  write_equations true equations;
  output_string channel
    ("]\nEnd\n\n" ^
     "Definition " ^ cexp_name ^ "_def:\n" ^
     "  " ^ cexp_name ^ " : compute_exp =\n    ");
  candle_registered_write_tasks channel [Candle_registered_exp call];
  output_string channel
    ("\nEnd\n\n" ^
     "Definition " ^ result_name ^ "_def:\n" ^
     "  " ^ result_name ^ " : cv =\n    ");
  candle_registered_write_tasks channel [Candle_registered_cv result];
  output_string channel "\nEnd\n\nval _ = export_theory ();\n";;

end;;
