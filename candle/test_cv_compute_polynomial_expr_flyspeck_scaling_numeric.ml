(* ========================================================================== *)
(* Larger six-variable numerical scaling probes for the reflected checker.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  The value program is checked against the       *)
(* theorem-producing source reifier.  Gradient and Hessian programs are       *)
(* generated externally from the same monomial data for profiling only; this  *)
(* file therefore makes no theorem/release claim about an accepted result.    *)
(* ========================================================================== *)

needs "candle/compute.ml";;
needs "candle/cv_compute_polynomial_expr_flyspeck_fixture.ml";;
needs "candle/cv_compute_whole_box_dim_taylor.ml";;

open Candle_cv_exact_interval_reify;;
open Candle_cv_whole_box_dim_taylor;;
open Candle_cv_polynomial_expr_flyspeck_fixture;;

let candle_nl_numeric_marker phase case_name item event =
  print_endline
    ("CANDLE_NL_NUMERIC_SCALE phase=" ^ phase ^
     " case=" ^ case_name ^ " item=" ^ item ^ " event=" ^ event);;

let candle_nl_numeric_vector = `p:real^6`;;

let candle_nl_numeric_variables =
  [`x1:real`;`x2:real`;`x3:real`;`x4:real`;`x5:real`;`x6:real`];;

let candle_nl_numeric_real_nat n =
  mk_comb (`(&):num->real`,mk_small_numeral n);;

let candle_nl_numeric_real_add left right =
  mk_binop `(+):real->real->real` left right;;

let candle_nl_numeric_real_mul left right =
  mk_binop `(*):real->real->real` left right;;

let rec candle_nl_numeric_product terms =
  match terms with
  | [] -> candle_nl_numeric_real_nat 1
  | [term] -> term
  | term::rest ->
      candle_nl_numeric_real_mul term (candle_nl_numeric_product rest);;

let rec candle_nl_numeric_sum terms =
  match terms with
  | [] -> candle_nl_numeric_real_nat 0
  | [term] -> term
  | term::rest -> candle_nl_numeric_real_add term (candle_nl_numeric_sum rest);;

let rec candle_nl_numeric_choose_repeated first degree =
  if degree = 0 then [[]]
  else if first > 5 then []
  else
    List.flatten
      (map
        (fun index ->
          map
            (fun rest -> index::rest)
            (candle_nl_numeric_choose_repeated index (degree - 1)))
        (first--5));;

let rec candle_nl_numeric_choose_distinct first degree =
  if degree = 0 then [[]]
  else if first > 5 then []
  else
    List.flatten
      (map
        (fun index ->
          map
            (fun rest -> index::rest)
            (candle_nl_numeric_choose_distinct (index + 1) (degree - 1)))
        (first--5));;

let candle_nl_numeric_base_coefficient indices =
  1 + itlist (fun index total -> index + 1 + total) indices 0;;

let candle_nl_numeric_quadratic =
  candle_nl_numeric_choose_repeated 0 2;;

let candle_nl_numeric_mixed =
  candle_nl_numeric_quadratic @
  candle_nl_numeric_choose_distinct 0 3 @
  [[0;0;1;1];[1;1;2;2];[2;2;3;3];
   [3;3;4;4];[4;4;5;5];[0;0;5;5]];;

let candle_nl_numeric_dense =
  candle_nl_numeric_quadratic @
  candle_nl_numeric_choose_repeated 0 3 @
  candle_nl_numeric_choose_distinct 0 4;;

let candle_nl_numeric_weighted monomials =
  map (fun indices -> candle_nl_numeric_base_coefficient indices,indices)
    monomials;;

let candle_nl_numeric_term_of_weighted_monomial (coefficient,indices) =
  candle_nl_numeric_real_mul
    (candle_nl_numeric_real_nat coefficient)
    (candle_nl_numeric_product
      (map (fun index -> List.nth candle_nl_numeric_variables index)
        indices));;

let candle_nl_numeric_term weighted negative_constant =
  candle_nl_numeric_real_add
    (candle_nl_numeric_sum
      (map candle_nl_numeric_term_of_weighted_monomial weighted))
    (mk_comb
      (`(--):real->real`,candle_nl_numeric_real_nat negative_constant));;

let rec candle_nl_numeric_remove_first target indices =
  match indices with
  | [] -> failwith "numeric derivative occurrence disappeared"
  | head::tail ->
      if head = target then tail
      else head::candle_nl_numeric_remove_first target tail;;

let candle_nl_numeric_occurrences target indices =
  itlist (fun index count -> if index = target then count + 1 else count)
    indices 0;;

let candle_nl_numeric_derivative di weighted =
  List.fold_right
    (fun (coefficient,indices) result ->
      let occurrences = candle_nl_numeric_occurrences di indices in
      if occurrences = 0 then result
      else
        (coefficient * occurrences,
         candle_nl_numeric_remove_first di indices)::result)
    weighted [];;

let candle_nl_numeric_program source =
  candle_q_compile_real_expression candle_nl_numeric_variables source;;

let candle_nl_numeric_numc n =
  mk_comb (`Cexp_num`,mk_numeral n);;

let candle_nl_numeric_numi n =
  candle_nl_numeric_numc (Num.num_of_int n);;

let candle_nl_numeric_pairc left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_nl_numeric_q_rep q =
  let z,d = dest_pair q in
  let p,n = dest_pair z in
  candle_nl_numeric_pairc
    (candle_nl_numeric_pairc
      (mk_comb (`Cexp_num`,p)) (mk_comb (`Cexp_num`,n)))
    (mk_comb (`Cexp_num`,d));;

let candle_nl_numeric_instruction_rep instruction =
  let constructor,arguments = strip_comb instruction in
  if aconv constructor `Candle_q_push` then
    match arguments with
    | [p;n;d] ->
        candle_nl_numeric_pairc (candle_nl_numeric_numi 0)
          (candle_nl_numeric_q_rep (mk_pair (mk_pair (p,n),d)))
    | _ -> failwith "malformed numeric push instruction"
  else if aconv constructor `Candle_q_load` then
    match arguments with
    | [index] ->
        candle_nl_numeric_pairc (candle_nl_numeric_numi 1)
          (mk_comb (`Cexp_num`,index))
    | _ -> failwith "malformed numeric load instruction"
  else if aconv instruction `Candle_q_neg` then candle_nl_numeric_numi 2
  else if aconv instruction `Candle_q_add` then candle_nl_numeric_numi 3
  else if aconv instruction `Candle_q_mul` then candle_nl_numeric_numi 4
  else if aconv instruction `Candle_q_square` then candle_nl_numeric_numi 5
  else failwith "unknown numeric scaling instruction";;

let candle_nl_numeric_list_rep render elements =
  itlist
    (fun element tail -> candle_nl_numeric_pairc (render element) tail)
    elements (candle_nl_numeric_numi 0);;

let candle_nl_numeric_program_rep program =
  candle_nl_numeric_list_rep candle_nl_numeric_instruction_rep program;;

let candle_nl_numeric_programs_rep programs =
  candle_nl_numeric_list_rep candle_nl_numeric_program_rep programs;;

let candle_nl_numeric_matrix_rep matrix =
  candle_nl_numeric_list_rep candle_nl_numeric_programs_rep matrix;;

let candle_nl_numeric_interval_rep interval =
  let lower,upper = dest_pair interval in
  candle_nl_numeric_pairc
    (candle_nl_numeric_q_rep lower) (candle_nl_numeric_q_rep upper);;

let candle_nl_numeric_boxes_rep boxes =
  candle_nl_numeric_list_rep candle_nl_numeric_interval_rep (dest_list boxes);;

let candle_nl_numeric_q numerator denominator =
  if denominator <= 0 then failwith "non-positive numeric-box denominator"
  else
    term_of_rat
      (Num.div_num
        (Num.num_of_int numerator)
        (Num.num_of_int denominator));;

let candle_nl_numeric_uniform_bounds lower_n lower_d upper_n upper_d =
  replicate (candle_nl_numeric_q lower_n lower_d) 6,
  replicate (candle_nl_numeric_q upper_n upper_d) 6;;

let candle_nl_numeric_prime_denominators = [127;131;137;139;149;151];;

let candle_nl_numeric_prime_lower =
  map (fun denominator -> candle_nl_numeric_q (~-1) denominator)
    candle_nl_numeric_prime_denominators;;

let candle_nl_numeric_prime_upper =
  map (fun denominator -> candle_nl_numeric_q 2 denominator)
    candle_nl_numeric_prime_denominators;;

let candle_nl_numeric_narrow_lower,candle_nl_numeric_narrow_upper =
  candle_nl_numeric_uniform_bounds (~-1) 16 1 16;;

let candle_nl_numeric_wide_lower,candle_nl_numeric_wide_upper =
  candle_nl_numeric_uniform_bounds (~-1) 2 1 2;;

let candle_nl_numeric_boxes =
  [("narrow-binary",candle_nl_numeric_narrow_lower,
                    candle_nl_numeric_narrow_upper);
   ("asymmetric-primes",candle_nl_numeric_prime_lower,
                         candle_nl_numeric_prime_upper);
   ("wide-binary",candle_nl_numeric_wide_lower,
                  candle_nl_numeric_wide_upper)];;

let candle_nl_numeric_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "unexpected numeric scaling result";;

let candle_nl_numeric_dest_unary expected tm =
  let operator,argument = dest_comb tm in
  if aconv operator expected then argument
  else failwith "unexpected numeric scaling unary result";;

let candle_nl_numeric_dest_num tm =
  dest_numeral (candle_nl_numeric_dest_unary `Cexp_num` tm);;

let candle_nl_numeric_num_bits n =
  let zero = Num.num_of_int 0 and two = Num.num_of_int 2 in
  let rec loop value bits =
    if Num.eq_num value zero then bits
    else loop (Num.quo_num value two) (bits + 1) in
  loop n 0;;

let candle_nl_numeric_upper_metrics upper =
  let z,d_encoded = candle_nl_numeric_dest_pair upper in
  let p_encoded,n_encoded = candle_nl_numeric_dest_pair z in
  let p = candle_nl_numeric_dest_num p_encoded and
      n = candle_nl_numeric_dest_num n_encoded and
      d = Num.add_num (candle_nl_numeric_dest_num d_encoded)
                      (Num.num_of_int 1) in
  candle_nl_numeric_num_bits p,
  candle_nl_numeric_num_bits n,
  candle_nl_numeric_num_bits d,
  String.length (Num.string_of_num p),
  String.length (Num.string_of_num n),
  String.length (Num.string_of_num d);;

let candle_nl_numeric_program_inventory pf pds pdds =
  let lengths =
    length pf :: map length pds @ List.flatten (map (map length) pdds) in
  length lengths,
  itlist (fun item total -> item + total) lengths 0,
  itlist (fun item current -> if item > current then item else current)
    lengths 0;;

let candle_nl_numeric_prepare case_name monomials negative_constant =
  let weighted = candle_nl_numeric_weighted monomials in
  let source = candle_nl_numeric_term weighted negative_constant in
  candle_nl_numeric_marker "source-reify" case_name "expression" "begin";
  let _,_,_,_,_,reified_value_program,_ =
    candle_poly_prepare_scalar_fixture
      candle_nl_numeric_vector candle_nl_numeric_variables source
      candle_nl_numeric_narrow_lower candle_nl_numeric_narrow_upper in
  candle_nl_numeric_marker "source-reify" case_name "expression" "end";
  candle_nl_numeric_marker "external-programs" case_name "expression" "begin";
  let pf = candle_nl_numeric_program source in
  if not
      (aconv
        (mk_list (pf,candle_q_instruction_type))
        reified_value_program) then
    failwith "numeric scaling value program disagrees with source reifier";
  let derivative_rows =
    map (fun di -> candle_nl_numeric_derivative di weighted) (0--5) in
  let pds =
    map
      (fun derivative ->
        candle_nl_numeric_program (candle_nl_numeric_term derivative 0))
      derivative_rows in
  let pdds =
    map
      (fun derivative ->
        map
          (fun dj ->
            candle_nl_numeric_program
              (candle_nl_numeric_term
                (candle_nl_numeric_derivative dj derivative) 0))
          (0--5))
      derivative_rows in
  let pf_rep = candle_nl_numeric_program_rep pf and
      pds_rep = candle_nl_numeric_programs_rep pds and
      pdds_rep = candle_nl_numeric_matrix_rep pdds in
  let programs,instructions,max_program =
    candle_nl_numeric_program_inventory pf pds pdds in
  candle_nl_numeric_marker "external-programs" case_name "expression" "end";
  print_endline
    ("CANDLE_NL_NUMERIC_SCALE_PREP case=" ^ case_name ^
     " monomials=" ^ string_of_int (length monomials) ^
     " programs=" ^ string_of_int programs ^
     " instructions=" ^ string_of_int instructions ^
     " max_program_instructions=" ^ string_of_int max_program ^
     " authority=unlinked-derivative-profile-only");
  pf_rep,pds_rep,pdds_rep;;

let candle_nl_numeric_run_box case_name box_name prepared lower upper =
  let pf_rep,pds_rep,pdds_rep = prepared in
  let boxes = candle_poly_fixture_q_boxes lower upper in
  let boxes_rep = candle_nl_numeric_boxes_rep boxes in
  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_whole_box_check`,
       [pf_rep;pds_rep;pdds_rep;boxes_rep]) in
  candle_nl_numeric_marker "compute" case_name box_name "begin";
  let compute_theorem =
    compute candle_cv_q_dim_whole_box_compute_eqs compute_tm in
  candle_nl_numeric_marker "compute" case_name box_name "end";
  let verdict,upper =
    candle_nl_numeric_dest_pair (rand (concl compute_theorem)) in
  let status = if aconv verdict `Cexp_num 1` then "accept" else "reject" in
  let p_bits,n_bits,d_bits,p_digits,n_digits,d_digits =
    candle_nl_numeric_upper_metrics upper in
  if hyp compute_theorem <> [] then
    failwith "numeric scaling compute theorem has assumptions";
  print_endline
    ("CANDLE_NL_NUMERIC_SCALE_RESULT case=" ^ case_name ^
     " box=" ^ box_name ^ " verdict=" ^ status ^
     " upper_term_chars=" ^ string_of_int (String.length (string_of_term upper)) ^
     " upper_p_bits=" ^ string_of_int p_bits ^
     " upper_n_bits=" ^ string_of_int n_bits ^
     " upper_d_bits=" ^ string_of_int d_bits ^
     " upper_p_digits=" ^ string_of_int p_digits ^
     " upper_n_digits=" ^ string_of_int n_digits ^
     " upper_d_digits=" ^ string_of_int d_digits ^
     " authority=unlinked-derivative-profile-only");;

let candle_nl_numeric_run_case case_name monomials negative_constant =
  candle_nl_numeric_marker "case" case_name "all" "begin";
  let prepared =
    candle_nl_numeric_prepare case_name monomials negative_constant in
  List.iter
    (fun (box_name,lower,upper) ->
      candle_nl_numeric_run_box case_name box_name prepared lower upper)
    candle_nl_numeric_boxes;
  candle_nl_numeric_marker "case" case_name "all" "end";;

let _ =
  candle_nl_numeric_run_case "quadratic-21" candle_nl_numeric_quadratic 128;;

let _ =
  candle_nl_numeric_run_case "mixed-47" candle_nl_numeric_mixed 512;;

let _ =
  candle_nl_numeric_run_case "dense-92" candle_nl_numeric_dense 2048;;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_FLYSPECK_SCALING_NUMERIC_OK";;
