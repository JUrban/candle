(* ========================================================================== *)
(* Untrusted ordinary executor for Candle compute equations.                 *)
(*                                                                            *)
(* DEVELOPMENT / DIAGNOSTIC ONLY.  This mirrors the public compute-equation  *)
(* language in ordinary ML so numerical execution can be compared with the   *)
(* monolithic Kernel.compute boundary.  It does not construct a theorem and  *)
(* must never authorize a proof result.  Every diagnostic use must compare   *)
(* its complete concrete output with Kernel.compute.                          *)
(* ========================================================================== *)

type candle_cv_diagnostic_value =
  | Candle_cv_diagnostic_num of num
  | Candle_cv_diagnostic_pair of
      candle_cv_diagnostic_value * candle_cv_diagnostic_value;;

type candle_cv_diagnostic_expression =
  | Candle_cv_diagnostic_const of num
  | Candle_cv_diagnostic_var of int
  | Candle_cv_diagnostic_pair_exp of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_add of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_sub of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_mul of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_div of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_mod of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_less of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_equal of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_fst of candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_snd of candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_ispair of candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_if of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression *
      candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_let of
      candle_cv_diagnostic_expression * candle_cv_diagnostic_expression
  | Candle_cv_diagnostic_app of
      int * candle_cv_diagnostic_expression list;;

type candle_cv_diagnostic_program = {
  candle_cv_diagnostic_names: string list;
  candle_cv_diagnostic_arities: int array;
  candle_cv_diagnostic_bodies: candle_cv_diagnostic_expression array
};;

type candle_cv_diagnostic_stats = {
  candle_cv_diagnostic_function_calls: int;
  candle_cv_diagnostic_pair_ops: int;
  candle_cv_diagnostic_add_ops: int;
  candle_cv_diagnostic_sub_ops: int;
  candle_cv_diagnostic_mul_ops: int;
  candle_cv_diagnostic_div_ops: int;
  candle_cv_diagnostic_mod_ops: int;
  candle_cv_diagnostic_less_ops: int;
  candle_cv_diagnostic_equal_ops: int;
  candle_cv_diagnostic_projection_ops: int;
  candle_cv_diagnostic_if_ops: int;
  candle_cv_diagnostic_let_ops: int;
  candle_cv_diagnostic_max_depth: int
};;

let candle_cv_diagnostic_constant_name tm =
  let name,_ = dest_const tm in name;;

let rec candle_cv_diagnostic_find_index item index = function
  | [] -> failwith ("cv diagnostic executor: missing item " ^ item)
  | head :: tail ->
      if item = head then index
      else candle_cv_diagnostic_find_index item (index + 1) tail;;

let rec candle_cv_diagnostic_find_term_index item index = function
  | [] -> failwith "cv diagnostic executor: free variable"
  | head :: tail ->
      if aconv item head then index
      else candle_cv_diagnostic_find_term_index item (index + 1) tail;;

let candle_cv_diagnostic_parse_equation theorem =
  let lhs,rhs = dest_eq (concl (SPEC_ALL theorem)) in
  let operator,arguments = strip_comb lhs in
  if not (is_const operator) || not (List.for_all is_var arguments) then
    failwith "cv diagnostic executor: malformed compute equation";
  candle_cv_diagnostic_constant_name operator,arguments,rhs;;

let candle_cv_diagnostic_compile equations =
  let rewritten = map (REWRITE_RULE [LET_END_DEF]) equations in
  let parsed = map candle_cv_diagnostic_parse_equation rewritten in
  let names = map (fun (name,_,_) -> name) parsed in
  let rec check_unique seen = function
    | [] -> ()
    | name :: tail ->
        if List.mem name seen then
          failwith "cv diagnostic executor: duplicate function name"
        else check_unique (name :: seen) tail in
  let _ = check_unique [] names in
  let function_index name =
    candle_cv_diagnostic_find_index name 0 names in
  let rec compile variables tm =
    if is_var tm then
      Candle_cv_diagnostic_var
        (candle_cv_diagnostic_find_term_index tm 0 variables)
    else if is_comb tm && is_abs (rator tm) then
      let variable,body = dest_abs (rator tm) in
      Candle_cv_diagnostic_let
        (compile variables (rand tm),compile (variable :: variables) body)
    else
      let operator,arguments = strip_comb tm in
      if not (is_const operator) then
        failwith "cv diagnostic executor: unsupported operator";
      let name = candle_cv_diagnostic_constant_name operator in
      if name = "LET" then
        (match arguments with
         | [abstraction;value] ->
             let variable,body = dest_abs abstraction in
             Candle_cv_diagnostic_let
               (compile variables value,
                compile (variable :: variables) body)
         | _ -> failwith "cv diagnostic executor: malformed LET")
      else if name = "Cexp_num" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_const (dest_numeral value)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_num")
      else if name = "Cexp_pair" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_pair_exp
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_pair")
      else if name = "Cexp_add" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_add
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_add")
      else if name = "Cexp_sub" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_sub
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_sub")
      else if name = "Cexp_mul" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_mul
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_mul")
      else if name = "Cexp_div" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_div
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_div")
      else if name = "Cexp_mod" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_mod
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_mod")
      else if name = "Cexp_less" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_less
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_less")
      else if name = "Cexp_eq" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_equal
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_eq")
      else if name = "Cexp_fst" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_fst (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_fst")
      else if name = "Cexp_snd" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_snd (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_snd")
      else if name = "Cexp_ispair" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_ispair (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_ispair")
      else if name = "Cexp_if" then
        (match arguments with
         | [condition;yes_value;no_value] ->
             Candle_cv_diagnostic_if
               (compile variables condition,
                compile variables yes_value,
                compile variables no_value)
         | _ -> failwith "cv diagnostic executor: malformed Cexp_if")
      else
        Candle_cv_diagnostic_app
          (function_index name,map (compile variables) arguments) in
  let arities =
    Array.of_list (map (fun (_,variables,_) -> length variables) parsed) in
  let bodies =
    Array.of_list
      (map (fun (_,variables,rhs) -> compile variables rhs) parsed) in
  {candle_cv_diagnostic_names = names;
   candle_cv_diagnostic_arities = arities;
   candle_cv_diagnostic_bodies = bodies};;

let candle_cv_diagnostic_compile_term program tm =
  let names = program.candle_cv_diagnostic_names in
  let function_index name =
    candle_cv_diagnostic_find_index name 0 names in
  let rec compile variables tm =
    if is_var tm then
      Candle_cv_diagnostic_var
        (candle_cv_diagnostic_find_term_index tm 0 variables)
    else if is_comb tm && is_abs (rator tm) then
      let variable,body = dest_abs (rator tm) in
      Candle_cv_diagnostic_let
        (compile variables (rand tm),compile (variable :: variables) body)
    else
      let operator,arguments = strip_comb tm in
      if not (is_const operator) then
        failwith "cv diagnostic executor: unsupported input operator";
      let name = candle_cv_diagnostic_constant_name operator in
      if name = "LET" then
        (match arguments with
         | [abstraction;value] ->
             let variable,body = dest_abs abstraction in
             Candle_cv_diagnostic_let
               (compile variables value,
                compile (variable :: variables) body)
         | _ -> failwith "cv diagnostic executor: malformed input LET")
      else if name = "Cexp_num" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_const (dest_numeral value)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_num")
      else if name = "Cexp_pair" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_pair_exp
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_pair")
      else if name = "Cexp_add" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_add
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_add")
      else if name = "Cexp_sub" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_sub
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_sub")
      else if name = "Cexp_mul" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_mul
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_mul")
      else if name = "Cexp_div" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_div
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_div")
      else if name = "Cexp_mod" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_mod
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_mod")
      else if name = "Cexp_less" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_less
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_less")
      else if name = "Cexp_eq" then
        (match arguments with
         | [left;right] ->
             Candle_cv_diagnostic_equal
               (compile variables left,compile variables right)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_eq")
      else if name = "Cexp_fst" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_fst (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_fst")
      else if name = "Cexp_snd" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_snd (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_snd")
      else if name = "Cexp_ispair" then
        (match arguments with
         | [value] -> Candle_cv_diagnostic_ispair (compile variables value)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_ispair")
      else if name = "Cexp_if" then
        (match arguments with
         | [condition;yes_value;no_value] ->
             Candle_cv_diagnostic_if
               (compile variables condition,
                compile variables yes_value,
                compile variables no_value)
         | _ -> failwith "cv diagnostic executor: malformed input Cexp_if")
      else
        Candle_cv_diagnostic_app
          (function_index name,map (compile variables) arguments) in
  compile [] tm;;

let rec candle_cv_diagnostic_value_equal left right =
  match left,right with
  | Candle_cv_diagnostic_num x,Candle_cv_diagnostic_num y -> Num.eq_num x y
  | Candle_cv_diagnostic_pair (lp,lq),
    Candle_cv_diagnostic_pair (rp,rq) ->
      candle_cv_diagnostic_value_equal lp rp &&
      candle_cv_diagnostic_value_equal lq rq
  | _ -> false;;

let candle_cv_diagnostic_execute program expression =
  let function_calls = ref 0 and pair_ops = ref 0 and add_ops = ref 0 and
      sub_ops = ref 0 and mul_ops = ref 0 and div_ops = ref 0 and
      mod_ops = ref 0 and less_ops = ref 0 and equal_ops = ref 0 and
      projection_ops = ref 0 and if_ops = ref 0 and let_ops = ref 0 and
      max_depth = ref 0 in
  let zero = Num.num_of_int 0 and one = Num.num_of_int 1 in
  let update_depth depth = if depth > !max_depth then max_depth := depth in
  let rec lookup index = function
    | [] -> failwith "cv diagnostic executor: environment underflow"
    | head :: tail -> if index = 0 then head else lookup (index - 1) tail in
  let as_num = function
    | Candle_cv_diagnostic_num n -> n
    | Candle_cv_diagnostic_pair _ -> zero in
  let rec evaluate depth environment = function
    | Candle_cv_diagnostic_const n ->
        update_depth depth; Candle_cv_diagnostic_num n
    | Candle_cv_diagnostic_var index ->
        update_depth depth; lookup index environment
    | Candle_cv_diagnostic_pair_exp (left,right) ->
        update_depth depth; pair_ops := !pair_ops + 1;
        Candle_cv_diagnostic_pair
          (evaluate (depth + 1) environment left,
           evaluate (depth + 1) environment right)
    | Candle_cv_diagnostic_add (left,right) ->
        update_depth depth; add_ops := !add_ops + 1;
        Candle_cv_diagnostic_num
          (Num.add_num
            (as_num (evaluate (depth + 1) environment left))
            (as_num (evaluate (depth + 1) environment right)))
    | Candle_cv_diagnostic_sub (left,right) ->
        update_depth depth; sub_ops := !sub_ops + 1;
        let x = as_num (evaluate (depth + 1) environment left) and
            y = as_num (evaluate (depth + 1) environment right) in
        Candle_cv_diagnostic_num
          (if Num.lt_num x y then zero else Num.sub_num x y)
    | Candle_cv_diagnostic_mul (left,right) ->
        update_depth depth; mul_ops := !mul_ops + 1;
        Candle_cv_diagnostic_num
          (Num.mul_num
            (as_num (evaluate (depth + 1) environment left))
            (as_num (evaluate (depth + 1) environment right)))
    | Candle_cv_diagnostic_div (left,right) ->
        update_depth depth; div_ops := !div_ops + 1;
        let x = as_num (evaluate (depth + 1) environment left) and
            y = as_num (evaluate (depth + 1) environment right) in
        Candle_cv_diagnostic_num
          (if Num.eq_num y zero then zero else Num.quo_num x y)
    | Candle_cv_diagnostic_mod (left,right) ->
        update_depth depth; mod_ops := !mod_ops + 1;
        let x = as_num (evaluate (depth + 1) environment left) and
            y = as_num (evaluate (depth + 1) environment right) in
        Candle_cv_diagnostic_num
          (if Num.eq_num y zero then x else Num.mod_num x y)
    | Candle_cv_diagnostic_less (left,right) ->
        update_depth depth; less_ops := !less_ops + 1;
        (match evaluate (depth + 1) environment left,
               evaluate (depth + 1) environment right with
         | Candle_cv_diagnostic_num x,Candle_cv_diagnostic_num y ->
             Candle_cv_diagnostic_num
               (if Num.lt_num x y then one else zero)
         | _ -> Candle_cv_diagnostic_num zero)
    | Candle_cv_diagnostic_equal (left,right) ->
        update_depth depth; equal_ops := !equal_ops + 1;
        Candle_cv_diagnostic_num
          (if candle_cv_diagnostic_value_equal
                (evaluate (depth + 1) environment left)
                (evaluate (depth + 1) environment right)
           then one else zero)
    | Candle_cv_diagnostic_fst value ->
        update_depth depth; projection_ops := !projection_ops + 1;
        (match evaluate (depth + 1) environment value with
         | Candle_cv_diagnostic_pair (left,_) -> left
         | _ -> Candle_cv_diagnostic_num zero)
    | Candle_cv_diagnostic_snd value ->
        update_depth depth; projection_ops := !projection_ops + 1;
        (match evaluate (depth + 1) environment value with
         | Candle_cv_diagnostic_pair (_,right) -> right
         | _ -> Candle_cv_diagnostic_num zero)
    | Candle_cv_diagnostic_ispair value ->
        update_depth depth; projection_ops := !projection_ops + 1;
        (match evaluate (depth + 1) environment value with
         | Candle_cv_diagnostic_pair _ -> Candle_cv_diagnostic_num one
         | _ -> Candle_cv_diagnostic_num zero)
    | Candle_cv_diagnostic_if (condition,yes_value,no_value) ->
        update_depth depth; if_ops := !if_ops + 1;
        (match evaluate (depth + 1) environment condition with
         | Candle_cv_diagnostic_num n when not (Num.eq_num n zero) ->
             evaluate (depth + 1) environment yes_value
         | _ -> evaluate (depth + 1) environment no_value)
    | Candle_cv_diagnostic_let (value,body) ->
        update_depth depth; let_ops := !let_ops + 1;
        let result = evaluate (depth + 1) environment value in
        evaluate (depth + 1) (result :: environment) body
    | Candle_cv_diagnostic_app (function_index,arguments) ->
        update_depth depth; function_calls := !function_calls + 1;
        let values = map (evaluate (depth + 1) environment) arguments in
        let arity = Array.get program.candle_cv_diagnostic_arities
            function_index in
        if length values <> arity then
          failwith "cv diagnostic executor: call arity mismatch";
        evaluate (depth + 1) values
          (Array.get program.candle_cv_diagnostic_bodies function_index) in
  let value = evaluate 0 [] expression in
  value,
  {candle_cv_diagnostic_function_calls = !function_calls;
   candle_cv_diagnostic_pair_ops = !pair_ops;
   candle_cv_diagnostic_add_ops = !add_ops;
   candle_cv_diagnostic_sub_ops = !sub_ops;
   candle_cv_diagnostic_mul_ops = !mul_ops;
   candle_cv_diagnostic_div_ops = !div_ops;
   candle_cv_diagnostic_mod_ops = !mod_ops;
   candle_cv_diagnostic_less_ops = !less_ops;
   candle_cv_diagnostic_equal_ops = !equal_ops;
   candle_cv_diagnostic_projection_ops = !projection_ops;
   candle_cv_diagnostic_if_ops = !if_ops;
   candle_cv_diagnostic_let_ops = !let_ops;
   candle_cv_diagnostic_max_depth = !max_depth};;

let rec candle_cv_diagnostic_value_term = function
  | Candle_cv_diagnostic_num value ->
      mk_comb (`Cexp_num`,mk_numeral value)
  | Candle_cv_diagnostic_pair (left,right) ->
      list_mk_comb
        (`Cexp_pair`,
         [candle_cv_diagnostic_value_term left;
          candle_cv_diagnostic_value_term right]);;

let candle_cv_diagnostic_stats_line label stats =
  print_endline
    ("CANDLE_CV_DIAGNOSTIC_EXECUTOR_STATS label=" ^ label ^
     " function_calls=" ^
       string_of_int stats.candle_cv_diagnostic_function_calls ^
     " pair_ops=" ^ string_of_int stats.candle_cv_diagnostic_pair_ops ^
     " add_ops=" ^ string_of_int stats.candle_cv_diagnostic_add_ops ^
     " sub_ops=" ^ string_of_int stats.candle_cv_diagnostic_sub_ops ^
     " mul_ops=" ^ string_of_int stats.candle_cv_diagnostic_mul_ops ^
     " div_ops=" ^ string_of_int stats.candle_cv_diagnostic_div_ops ^
     " mod_ops=" ^ string_of_int stats.candle_cv_diagnostic_mod_ops ^
     " less_ops=" ^ string_of_int stats.candle_cv_diagnostic_less_ops ^
     " equal_ops=" ^ string_of_int stats.candle_cv_diagnostic_equal_ops ^
     " projection_ops=" ^
       string_of_int stats.candle_cv_diagnostic_projection_ops ^
     " if_ops=" ^ string_of_int stats.candle_cv_diagnostic_if_ops ^
     " let_ops=" ^ string_of_int stats.candle_cv_diagnostic_let_ops ^
     " max_depth=" ^ string_of_int stats.candle_cv_diagnostic_max_depth);;
