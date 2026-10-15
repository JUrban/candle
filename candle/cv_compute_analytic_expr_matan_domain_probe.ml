(* ========================================================================== *)
(* Conservative source-box range probe for residual Flyspeck [matan] calls. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This is an untrusted planning diagnostic.     *)
(* Every eventual checker result must still be authenticated by the kernel.  *)
(* ========================================================================== *)

module Candle_cv_analytic_expr_matan_domain_probe = struct

open Candle_cv_flyspeck_direct_source_compat;;
open Candle_cv_exact_interval_reify;;

let candle_nl_matan_source_ids =
  ["prep-5202826650 a";
   "prep-7796879304";
   "prep-QZECFIC wt0";
   "prep-QZECFIC wt0 corner";
   "prep-QZECFIC wt0 sqrt8";
   "prep-QZECFIC wt1 split(0/2)";
   "prep-QZECFIC wt1 split(1/2)";
   "prep-QZECFIC wt2 A split(0/4)";
   "prep-QZECFIC wt2 A split(1/4)";
   "prep-QZECFIC wt2 A split(2/4)";
   "prep-QZECFIC wt2 A split(3/4)";
   "prep-TSKAJXY-GXSABWC DIV"];;

let candle_nl_matan_defs =
  candle_direct_flyspeck_defs @
  Break_case_exec.nonlin_rewrites @
  map snd Break_case_exec.trig_expansions1 @
  [Sphere.sqrt8;
   Sphere.sqrt2;
   Sphere.sqrt3;
   Sphere.tau0;
   Sphere.mm1;
   Sphere.mm2;
   Sphere.h0;
   Sphere.hplus;
   Sphere.rh0;
   Sphere.rotate4;
   Sphere.rotate5;
   Sphere.rotate6];;

let candle_nl_matan_target source_id =
  let _,preparation,needs_delta = Break_case_exec.get_case source_id in
  Break_case_exec.run_generic
    (fun selected -> preparation selected) needs_delta source_id;;

let candle_nl_matan_target_parts target =
  let stripped = snd (strip_forall target) in
  let head,arguments = strip_comb stripped in
  let name =
    if is_const head then fst (dest_const head)
    else failwith "matan domain probe: nonconstant target head" in
  match name,arguments with
  | "ineqm",[variables;bounds;formula] ->
      let variables = dest_list variables in
      let bounds = map dest_pair (dest_list bounds) in
      if length variables <> length bounds then
        failwith "matan domain probe: variable/bound shape";
      variables,bounds,formula
  | "ineq",[encoded_bounds;formula] ->
      let triples =
        map
          (fun encoded ->
            let lower,rest = dest_pair encoded in
            let variable,upper = dest_pair rest in
            lower,variable,upper)
          (dest_list encoded_bounds) in
      let variables = map (fun (_,variable,_) -> variable) triples and
          bounds = map (fun (lower,_,upper) -> lower,upper) triples in
      variables,bounds,formula
  | _ ->
      failwith
        ("matan domain probe: bad target shape head=" ^ name ^
         " arity=" ^ string_of_int (length arguments));;

let candle_nl_matan_expand formula =
  let expansion =
    (REWRITE_CONV
       [TAUT `(P ==> Q) <=> (~P \/ Q)`;
        REAL_ARITH `~(a > b:real) <=> a <= b`;
        REAL_ARITH `~(a < b:real) <=> b <= a`;
        REAL_ARITH `~(a >= b:real) <=> a < b`;
        REAL_ARITH `~(a <= b:real) <=> b < a`]
     THENC candle_direct_expand_ineq_case
     THENC REWRITE_CONV candle_nl_matan_defs
     THENC DEPTH_CONV let_CONV)
      formula in
  rand (concl expansion);;

let rec candle_nl_matan_subterms tm =
  let here =
    if is_comb tm then
      let head,arguments = strip_comb tm in
      if is_const head && fst (dest_const head) = "matan" then
        match arguments with
        | [argument] -> [argument]
        | _ -> failwith "matan domain probe: bad matan arity"
      else []
    else [] in
  if not (here = []) then here
  else if is_comb tm then
    candle_nl_matan_subterms (rator tm) @
    candle_nl_matan_subterms (rand tm)
  else if is_abs tm then
    candle_nl_matan_subterms (body tm)
  else [];;

let candle_nl_matan_q_zero = Num.num_of_int 0;;

let candle_nl_matan_is_unary operator tm =
  try Candle_cv_exact_interval_reify.candle_q_is_unary operator tm
  with Failure _ -> false;;

let candle_nl_matan_is_binary operator tm =
  try Candle_cv_exact_interval_reify.candle_q_is_binary operator tm
  with Failure _ -> false;;

let candle_nl_matan_exact_rational tm =
  try rat_of_term tm with Failure _ ->
  if candle_nl_matan_is_binary `DECIMAL` tm then
    Candle_cv_exact_interval_reify.candle_q_decimal_rational tm
  else More_float.num_of_float_tm tm;;

let candle_nl_matan_interval_neg (lower,upper) =
  Num.minus_num upper,Num.minus_num lower;;

let candle_nl_matan_interval_add (ll,lu) (rl,ru) =
  Num.add_num ll rl,Num.add_num lu ru;;

let candle_nl_matan_interval_mul (ll,lu) (rl,ru) =
  let products =
    [Num.mul_num ll rl; Num.mul_num ll ru;
     Num.mul_num lu rl; Num.mul_num lu ru] in
  itlist Num.min_num (tl products) (hd products),
  itlist Num.max_num (tl products) (hd products);;

let candle_nl_matan_interval_square (lower,upper) =
  let lower_squared = Num.mul_num lower lower and
      upper_squared = Num.mul_num upper upper in
  if Num.le_num lower candle_nl_matan_q_zero &&
     Num.le_num candle_nl_matan_q_zero upper then
    candle_nl_matan_q_zero,Num.max_num lower_squared upper_squared
  else
    Num.min_num lower_squared upper_squared,
    Num.max_num lower_squared upper_squared;;

let candle_nl_matan_interval_inv (lower,upper) =
  if Num.le_num lower candle_nl_matan_q_zero &&
     Num.le_num candle_nl_matan_q_zero upper then
    failwith "denominator interval contains zero";
  Num.div_num (Num.num_of_int 1) upper,
  Num.div_num (Num.num_of_int 1) lower;;

let candle_nl_matan_float_value tm =
  try Some (More_float.num_of_float_tm tm)
  with Failure _ -> None;;

let rec candle_nl_matan_interval_eval environment tm =
  try assoc tm environment with Failure _ ->
  if is_ratconst tm then
    let value = rat_of_term tm in value,value
  else if candle_nl_matan_is_binary `DECIMAL` tm then
    let value =
      Candle_cv_exact_interval_reify.candle_q_decimal_rational tm in
    value,value
  else match candle_nl_matan_float_value tm with
  | Some value -> value,value
  | None ->
  if candle_nl_matan_is_unary
            `(--):real->real` tm then
    candle_nl_matan_interval_neg
      (candle_nl_matan_interval_eval environment (rand tm))
  else if candle_nl_matan_is_unary
            `inv:real->real` tm then
    candle_nl_matan_interval_inv
      (candle_nl_matan_interval_eval environment (rand tm))
  else if candle_nl_matan_is_binary
            `(+):real->real->real` tm then
    let left,right =
      Candle_cv_exact_interval_reify.candle_q_dest_binary
        `(+):real->real->real` tm in
    candle_nl_matan_interval_add
      (candle_nl_matan_interval_eval environment left)
      (candle_nl_matan_interval_eval environment right)
  else if candle_nl_matan_is_binary
            `(-):real->real->real` tm then
    let left,right =
      Candle_cv_exact_interval_reify.candle_q_dest_binary
        `(-):real->real->real` tm in
    candle_nl_matan_interval_add
      (candle_nl_matan_interval_eval environment left)
      (candle_nl_matan_interval_neg
        (candle_nl_matan_interval_eval environment right))
  else if candle_nl_matan_is_binary
            `(*):real->real->real` tm then
    let left,right =
      Candle_cv_exact_interval_reify.candle_q_dest_binary
        `(*):real->real->real` tm in
    candle_nl_matan_interval_mul
      (candle_nl_matan_interval_eval environment left)
      (candle_nl_matan_interval_eval environment right)
  else if candle_nl_matan_is_binary
            `(/):real->real->real` tm then
    let left,right =
      Candle_cv_exact_interval_reify.candle_q_dest_binary
        `(/):real->real->real` tm in
    candle_nl_matan_interval_mul
      (candle_nl_matan_interval_eval environment left)
      (candle_nl_matan_interval_inv
        (candle_nl_matan_interval_eval environment right))
  else if candle_nl_matan_is_binary
            `(pow):real->num->real` tm then
    let base,exponent =
      Candle_cv_exact_interval_reify.candle_q_dest_binary
        `(pow):real->num->real` tm in
    if not (is_numeral exponent && dest_small_numeral exponent = 2) then
      failwith "unsupported power";
    candle_nl_matan_interval_square
      (candle_nl_matan_interval_eval environment base)
  else failwith ("unsupported argument term: " ^ string_of_term tm);;

let candle_nl_matan_interval_string value =
  Num.string_of_num value;;

let candle_nl_matan_emit source_id =
  try
    let target =
      try candle_nl_matan_target source_id
      with Failure message -> failwith ("target: " ^ message) in
    let variables,bound_terms,formula =
      try candle_nl_matan_target_parts target
      with Failure message -> failwith ("target_parts: " ^ message) in
    let bounds =
      try
        map
          (fun (lower,upper) ->
            let exact_value side tm =
              let expanded =
                try rand (concl (REWRITE_CONV candle_nl_matan_defs tm))
                with Failure message ->
                  failwith
                    (side ^ "_rewrite=" ^ string_of_term tm ^ ": " ^
                     message) in
              let value_lower,value_upper =
                try candle_nl_matan_interval_eval [] expanded
                with Failure message ->
                  failwith
                    (side ^ "=" ^ string_of_term expanded ^ ": " ^ message) in
              if not (Num.eq_num value_lower value_upper) then
                failwith (side ^ " is not exact");
              value_lower in
            let lower_value =
              try exact_value "lower" lower
              with Failure message ->
                failwith
                  ("lower=" ^ string_of_term lower ^ ": " ^ message) in
            let upper_value =
              try exact_value "upper" upper
              with Failure message ->
                failwith
                  ("upper=" ^ string_of_term upper ^ ": " ^ message) in
            lower_value,upper_value)
          bound_terms
      with Failure message -> failwith ("bounds: " ^ message) in
    let expanded =
      try candle_nl_matan_expand formula
      with Failure message -> failwith ("expand: " ^ message) in
    let arguments =
      try candle_nl_matan_subterms expanded
      with Failure message -> failwith ("subterms: " ^ message) in
    let environment = zip variables bounds in
    if arguments = [] then
      print_endline
        ("CANDLE_NL_MATAN_DOMAIN_PROBE_ERROR DEVELOPMENT_NON_RELEASE" ^
         " source_id=" ^ source_id ^ " message=no_matan_after_expansion")
    else
      do_list
        (fun (index,argument) ->
          try
            let lower,upper =
              candle_nl_matan_interval_eval environment argument in
            let sign =
              if Num.lt_num candle_nl_matan_q_zero lower then "positive"
              else if Num.lt_num upper candle_nl_matan_q_zero then "negative"
              else "crosses_zero" in
            print_endline
              ("CANDLE_NL_MATAN_DOMAIN_PROBE DEVELOPMENT_NON_RELEASE" ^
               " source_id=" ^ source_id ^
               " occurrence=" ^ string_of_int index ^
               " lower=" ^ candle_nl_matan_interval_string lower ^
               " upper=" ^ candle_nl_matan_interval_string upper ^
               " sign=" ^ sign ^
               " argument=" ^ string_of_term argument)
          with Failure message ->
            print_endline
              ("CANDLE_NL_MATAN_DOMAIN_PROBE_ERROR DEVELOPMENT_NON_RELEASE" ^
               " source_id=" ^ source_id ^
               " occurrence=" ^ string_of_int index ^
               " message=" ^ message))
        (zip (0--(length arguments - 1)) arguments)
  with Failure message ->
    print_endline
      ("CANDLE_NL_MATAN_DOMAIN_PROBE_ERROR DEVELOPMENT_NON_RELEASE" ^
       " source_id=" ^ source_id ^ " message=" ^ message);;

let _ = do_list candle_nl_matan_emit candle_nl_matan_source_ids;;

end;;
