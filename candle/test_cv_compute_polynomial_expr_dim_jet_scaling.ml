(* Larger six-coordinate throughput probe for the reflected shared jets.      *)
(* DEVELOPMENT / NON-RELEASE: final analytic acceptance is still pending.     *)

needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_reify.ml";;
needs "candle/cv_compute_polynomial_expr_dim_jet_compute.ml";;
needs "candle/cv_compute_polynomial_expr_dim_first_jet_compute.ml";;

open Candle_cv_exact_interval_reify;;
open Candle_cv_exact_interval_program;;
open Candle_cv_polynomial_expr_dim_jet_compute;;
open Candle_cv_polynomial_expr_dim_first_jet_compute;;

let candle_dim_jet_scale_marker phase case_name box_name event =
  print_endline
    ("CANDLE_DIM_JET_SCALE phase=" ^ phase ^
     " case=" ^ case_name ^ " box=" ^ box_name ^ " event=" ^ event);;

let rec candle_dim_jet_scale_choose_repeated first degree =
  if degree = 0 then [[]]
  else if first > 5 then []
  else
    List.flatten
      (map
        (fun index ->
          map
            (fun rest -> index::rest)
            (candle_dim_jet_scale_choose_repeated index (degree - 1)))
        (first--5));;

let rec candle_dim_jet_scale_choose_distinct first degree =
  if degree = 0 then [[]]
  else if first > 5 then []
  else
    List.flatten
      (map
        (fun index ->
          map
            (fun rest -> index::rest)
            (candle_dim_jet_scale_choose_distinct (index + 1) (degree - 1)))
        (first--5));;

let candle_dim_jet_scale_quadratic =
  candle_dim_jet_scale_choose_repeated 0 2;;

let candle_dim_jet_scale_mixed =
  candle_dim_jet_scale_quadratic @
  candle_dim_jet_scale_choose_distinct 0 3 @
  [[0;0;1;1];[1;1;2;2];[2;2;3;3];
   [3;3;4;4];[4;4;5;5];[0;0;5;5]];;

let candle_dim_jet_scale_dense =
  candle_dim_jet_scale_quadratic @
  candle_dim_jet_scale_choose_repeated 0 3 @
  candle_dim_jet_scale_choose_distinct 0 4;;

let candle_dim_jet_scale_degree2_through4 =
  candle_dim_jet_scale_quadratic @
  candle_dim_jet_scale_choose_repeated 0 3 @
  candle_dim_jet_scale_choose_repeated 0 4;;

let candle_dim_jet_scale_degree2_through5 =
  candle_dim_jet_scale_degree2_through4 @
  candle_dim_jet_scale_choose_repeated 0 5;;

let candle_dim_jet_scale_degree2_through6 =
  candle_dim_jet_scale_degree2_through5 @
  candle_dim_jet_scale_choose_repeated 0 6;;

let candle_dim_jet_scale_degree2_through7 =
  candle_dim_jet_scale_degree2_through6 @
  candle_dim_jet_scale_choose_repeated 0 7;;

let candle_dim_jet_scale_coefficient indices =
  1 + itlist (fun index total -> index + 1 + total) indices 0;;

let candle_dim_jet_scale_push positive negative =
  list_mk_comb
    (`Candle_q_push`,
     [mk_small_numeral positive;mk_small_numeral negative;`0`]);;

let candle_dim_jet_scale_load index =
  mk_comb (`Candle_q_load`,mk_small_numeral index);;

let candle_dim_jet_scale_monomial indices =
  let coefficient = candle_dim_jet_scale_coefficient indices in
  candle_dim_jet_scale_push coefficient 0 ::
  List.flatten
    (map
      (fun index -> [candle_dim_jet_scale_load index;`Candle_q_mul`])
      indices);;

let candle_dim_jet_scale_sum monomials =
  match monomials with
  | [] -> [candle_dim_jet_scale_push 0 0]
  | first::rest ->
      List.fold_left
        (fun program monomial ->
          program @ candle_dim_jet_scale_monomial monomial @
          [`Candle_q_add`])
        (candle_dim_jet_scale_monomial first) rest;;

let candle_dim_jet_scale_program monomials negative_constant =
  candle_dim_jet_scale_sum monomials @
  [candle_dim_jet_scale_push 0 negative_constant;`Candle_q_add`];;

let candle_dim_jet_scale_numc n =
  mk_comb (`Cexp_num`,n);;

let candle_dim_jet_scale_pairc left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_dim_jet_scale_q_rep rational =
  let z,d = dest_pair (candle_q_term rational) in
  let p,n = dest_pair z in
  candle_dim_jet_scale_pairc
    (candle_dim_jet_scale_pairc
      (candle_dim_jet_scale_numc p) (candle_dim_jet_scale_numc n))
    (candle_dim_jet_scale_numc d);;

let candle_dim_jet_scale_interval_rep lower upper =
  candle_dim_jet_scale_pairc
    (candle_dim_jet_scale_q_rep lower)
    (candle_dim_jet_scale_q_rep upper);;

let candle_dim_jet_scale_list_rep elements =
  itlist
    (fun element tail -> candle_dim_jet_scale_pairc element tail)
    elements `Cexp_num 0`;;

let candle_dim_jet_scale_q numerator denominator =
  Num.div_num (Num.num_of_int numerator) (Num.num_of_int denominator);;

let candle_dim_jet_scale_box_rep lower upper =
  candle_dim_jet_scale_list_rep
    (map2 candle_dim_jet_scale_interval_rep lower upper);;

let candle_dim_jet_scale_narrow_lower =
  replicate (candle_dim_jet_scale_q (~-1) 16) 6;;
let candle_dim_jet_scale_narrow_upper =
  replicate (candle_dim_jet_scale_q 1 16) 6;;
let candle_dim_jet_scale_wide_lower =
  replicate (candle_dim_jet_scale_q (~-1) 2) 6;;
let candle_dim_jet_scale_wide_upper =
  replicate (candle_dim_jet_scale_q 1 2) 6;;
let candle_dim_jet_scale_primes = [127;131;137;139;149;151];;
let candle_dim_jet_scale_prime_lower =
  map (fun denominator -> candle_dim_jet_scale_q (~-1) denominator)
    candle_dim_jet_scale_primes;;
let candle_dim_jet_scale_prime_upper =
  map (fun denominator -> candle_dim_jet_scale_q 2 denominator)
    candle_dim_jet_scale_primes;;

let candle_dim_jet_scale_boxes =
  [("narrow-binary",candle_dim_jet_scale_narrow_lower,
                    candle_dim_jet_scale_narrow_upper);
   ("asymmetric-primes",candle_dim_jet_scale_prime_lower,
                         candle_dim_jet_scale_prime_upper);
   ("wide-binary",candle_dim_jet_scale_wide_lower,
                  candle_dim_jet_scale_wide_upper)];;

let candle_dim_jet_scale_binary_boxes =
  [("narrow-binary",candle_dim_jet_scale_narrow_lower,
                    candle_dim_jet_scale_narrow_upper);
   ("wide-binary",candle_dim_jet_scale_wide_lower,
                  candle_dim_jet_scale_wide_upper)];;

let candle_dim_jet_scale_dest_pair tm =
  let partial,right = dest_comb tm in
  let operator,left = dest_comb partial in
  if aconv operator `Cexp_pair` then left,right
  else failwith "unexpected dimension-jet scaling result";;

let candle_dim_jet_scale_dest_unary expected tm =
  let operator,argument = dest_comb tm in
  if aconv operator expected then argument
  else failwith "unexpected dimension-jet scaling unary result";;

let candle_dim_jet_scale_dest_num tm =
  dest_numeral
    (candle_dim_jet_scale_dest_unary `Cexp_num` tm);;

let candle_dim_jet_scale_num_bits n =
  let zero = Num.num_of_int 0 and two = Num.num_of_int 2 in
  let rec loop value bits =
    if Num.eq_num value zero then bits
    else loop (Num.quo_num value two) (bits + 1) in
  loop n 0;;

let candle_dim_jet_scale_upper_metrics upper =
  let z,d_encoded = candle_dim_jet_scale_dest_pair upper in
  let p_encoded,n_encoded = candle_dim_jet_scale_dest_pair z in
  let p = candle_dim_jet_scale_dest_num p_encoded and
      n = candle_dim_jet_scale_dest_num n_encoded and
      d = Num.add_num (candle_dim_jet_scale_dest_num d_encoded)
                      (Num.num_of_int 1) in
  candle_dim_jet_scale_num_bits p,
  candle_dim_jet_scale_num_bits n,
  candle_dim_jet_scale_num_bits d;;

let candle_dim_jet_scale_run_box case_name box_name program_rep lower upper =
  let boxes_rep = candle_dim_jet_scale_box_rep lower upper in
  let compute_tm =
    list_mk_comb
      (`candle_cv_q_dim_first_jet_whole_box_check`,
       [program_rep;boxes_rep]) in
  candle_dim_jet_scale_marker "compute" case_name box_name "begin";
  let started = Unix.gettimeofday () in
  let compute_theorem =
    compute candle_cv_q_dim_first_jet_compute_eqs compute_tm in
  let elapsed = Unix.gettimeofday () -. started in
  candle_dim_jet_scale_marker "compute" case_name box_name "end";
  let verdict,upper =
    candle_dim_jet_scale_dest_pair (rand (concl compute_theorem)) in
  let p_bits,n_bits,d_bits =
    candle_dim_jet_scale_upper_metrics upper in
  if hyp compute_theorem <> [] then
    failwith "dimension-jet scaling compute theorem has assumptions";
  print_endline
    ("CANDLE_DIM_JET_SCALE_RESULT case=" ^ case_name ^
     " box=" ^ box_name ^
     " verdict=" ^
       (if aconv verdict `Cexp_num 1` then "accept" else "reject") ^
     " compute_seconds=" ^ string_of_float elapsed ^
     " upper_term_chars=" ^ string_of_int (String.length (string_of_term upper)) ^
     " upper_p_bits=" ^ string_of_int p_bits ^
     " upper_n_bits=" ^ string_of_int n_bits ^
     " upper_d_bits=" ^ string_of_int d_bits ^
     " authority=cval-and-source-jet-semantics-proved-analytic-finish-pending");;

let rec candle_dim_jet_scale_chunks width items =
  if items = [] then []
  else
    let count = min width (length items) in
    let chunk,rest = chop_list count items in
    chunk::candle_dim_jet_scale_chunks width rest;;

let candle_dim_jet_scale_compute_ground phase case_name box_name tm =
  candle_dim_jet_scale_marker phase case_name box_name "begin";
  let th = compute candle_cv_q_dim_jet_compute_eqs tm in
  candle_dim_jet_scale_marker phase case_name box_name "end";
  if hyp th <> [] then
    failwith "dimension-jet chunk theorem has assumptions";
  rand (concl th);;

let candle_dim_first_jet_scale_compute_ground
      phase case_name box_name tm =
  candle_dim_jet_scale_marker phase case_name box_name "begin";
  let th = compute candle_cv_q_dim_first_jet_compute_eqs tm in
  candle_dim_jet_scale_marker phase case_name box_name "end";
  if hyp th <> [] then
    failwith "dimension first-jet chunk theorem has assumptions";
  rand (concl th);;

let candle_dim_jet_scale_run_chunks
      case_name box_name boxes_rep encoded_chunks =
  let rec run index stack chunks =
    match chunks with
    | [] ->
        candle_dim_jet_scale_compute_ground
          "chunk-head" case_name box_name
          (list_mk_comb
            (`candle_cv_q_dim_jet_head`,[boxes_rep;stack]))
    | chunk::rest ->
        let next_stack =
          candle_dim_jet_scale_compute_ground
            ("chunk-" ^ string_of_int index) case_name box_name
            (list_mk_comb
              (`candle_cv_q_dim_jet_run`,
               [boxes_rep;chunk;stack])) in
        run (index + 1) next_stack rest in
  run 0 `Cexp_num 0` encoded_chunks;;

let candle_dim_first_jet_scale_run_chunks
      case_name box_name boxes_rep encoded_chunks =
  let rec run index stack chunks =
    match chunks with
    | [] ->
        candle_dim_first_jet_scale_compute_ground
          "first-chunk-head" case_name box_name
          (list_mk_comb
            (`candle_cv_q_dim_first_jet_head`,[boxes_rep;stack]))
    | chunk::rest ->
        let next_stack =
          candle_dim_first_jet_scale_compute_ground
            ("first-chunk-" ^ string_of_int index) case_name box_name
            (list_mk_comb
              (`candle_cv_q_dim_first_jet_run`,
               [boxes_rep;chunk;stack])) in
        run (index + 1) next_stack rest in
  run 0 `Cexp_num 0` encoded_chunks;;

let candle_dim_jet_scale_run_center_profile
      case_name monomials negative_constant chunk_width =
  let program = candle_dim_jet_scale_program monomials negative_constant in
  let chunks = candle_dim_jet_scale_chunks chunk_width program in
  let encoded_chunks =
    map
      (fun chunk ->
        rand
          (concl
            (candle_q_program_encode_conv
              (mk_list (chunk,candle_q_instruction_type)))))
      chunks in
  let boxes_rep =
    candle_dim_jet_scale_box_rep
      candle_dim_jet_scale_narrow_lower candle_dim_jet_scale_narrow_upper in
  let center_rep_raw =
    candle_dim_jet_scale_compute_ground
      "profile-center-environment" case_name "narrow-binary"
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_rep)) in
  let center_rep =
    candle_dim_jet_scale_compute_ground
      "profile-center-normalize" case_name "narrow-binary"
      (mk_comb (`candle_cv_q_interval_list_normalize`,center_rep_raw)) in
  let first_jet =
    candle_dim_first_jet_scale_run_chunks
      case_name "narrow-binary-first" center_rep encoded_chunks in
  let full_jet =
    candle_dim_jet_scale_run_chunks
      case_name "narrow-binary-full" center_rep encoded_chunks in
  let full_projection =
    candle_dim_jet_scale_pairc
      (mk_comb (`Cexp_fst`,full_jet))
      (mk_comb (`Cexp_fst`,mk_comb (`Cexp_snd`,full_jet))) in
  let projection_th =
    compute candle_cv_q_dim_first_jet_compute_eqs full_projection in
  let projected = rand (concl projection_th) in
  if hyp projection_th <> [] then
    failwith "dimension first-jet projection theorem has assumptions";
  if not (aconv first_jet projected) then
    failwith "dimension first-jet result differs from full-jet projection";
  print_endline
    ("CANDLE_DIM_FIRST_JET_PROFILE case=" ^ case_name ^
     " box=narrow-binary" ^
     " instructions=" ^ string_of_int (length program) ^
     " chunks=" ^ string_of_int (length chunks) ^
     " first_term_chars=" ^
       string_of_int (String.length (string_of_term first_jet)) ^
     " full_term_chars=" ^
       string_of_int (String.length (string_of_term full_jet)) ^
     " projection_match=true" ^
     " authority=universal-projection-proved-separately-development-non-release");;

let candle_dim_jet_scale_run_box_chunked
      case_name box_name encoded_chunks lower upper =
  let boxes_rep = candle_dim_jet_scale_box_rep lower upper in
  let center_rep_raw =
    candle_dim_jet_scale_compute_ground
      "center-environment" case_name box_name
      (mk_comb (`candle_cv_q_center_environment_list`,boxes_rep)) in
  let center_rep =
    candle_dim_jet_scale_compute_ground
      "center-normalize" case_name box_name
      (mk_comb (`candle_cv_q_interval_list_normalize`,center_rep_raw)) in
  let radii_rep_raw =
    candle_dim_jet_scale_compute_ground
      "radii" case_name box_name
      (mk_comb (`candle_cv_q_radius_list`,boxes_rep)) in
  let radii_rep =
    candle_dim_jet_scale_compute_ground
      "radii-normalize" case_name box_name
      (mk_comb (`candle_cv_q_list_normalize`,radii_rep_raw)) in
  let valid_rep =
    candle_dim_jet_scale_compute_ground
      "box-valid" case_name box_name
      (mk_comb (`candle_cv_q_box_valid_list`,boxes_rep)) in
  let center_jet =
    candle_dim_first_jet_scale_run_chunks
      case_name (box_name ^ "-center") center_rep encoded_chunks in
  let box_jet =
    candle_dim_jet_scale_run_chunks
      case_name (box_name ^ "-box") boxes_rep encoded_chunks in
  let upper =
    candle_dim_first_jet_scale_compute_ground
      "taylor-handoff" case_name box_name
      (list_mk_comb
        (`candle_cv_q_dim_first_jet_taylor_upper`,
         [radii_rep;center_jet;box_jet])) in
  let result =
    candle_dim_jet_scale_compute_ground
      "finish" case_name box_name
      (list_mk_comb
        (`candle_cv_q_dim_whole_box_finish`,
         [`Cexp_num 1`;valid_rep;upper])) in
  let verdict,final_upper = candle_dim_jet_scale_dest_pair result in
  let p_bits,n_bits,d_bits =
    candle_dim_jet_scale_upper_metrics final_upper in
  print_endline
    ("CANDLE_DIM_JET_CHUNKED_RESULT case=" ^ case_name ^
     " box=" ^ box_name ^
     " chunks=" ^ string_of_int (length encoded_chunks) ^
     " verdict=" ^
       (if aconv verdict `Cexp_num 1` then "accept" else "reject") ^
     " upper_term_chars=" ^
       string_of_int (String.length (string_of_term final_upper)) ^
     " upper_p_bits=" ^ string_of_int p_bits ^
     " upper_n_bits=" ^ string_of_int n_bits ^
     " upper_d_bits=" ^ string_of_int d_bits ^
     " authority=cval-and-source-jet-semantics-proved-analytic-finish-pending");;

let candle_dim_jet_scale_run_case_chunked_on_boxes
      case_name monomials negative_constant chunk_width boxes =
  candle_dim_jet_scale_marker "chunk-prepare" case_name "all" "begin";
  let program = candle_dim_jet_scale_program monomials negative_constant in
  let chunks = candle_dim_jet_scale_chunks chunk_width program in
  let encoded_chunks =
    map
      (fun chunk ->
        rand
          (concl
            (candle_q_program_encode_conv
              (mk_list (chunk,candle_q_instruction_type)))))
      chunks in
  candle_dim_jet_scale_marker "chunk-prepare" case_name "all" "end";
  print_endline
    ("CANDLE_DIM_JET_CHUNKED_PREP case=" ^ case_name ^
     " monomials=" ^ string_of_int (length monomials) ^
     " instructions=" ^ string_of_int (length program) ^
     " chunk_width=" ^ string_of_int chunk_width ^
     " chunks=" ^ string_of_int (length chunks) ^
     " encoded_term_chars=" ^
       string_of_int
         (itlist
           (fun chunk total ->
             String.length (string_of_term chunk) + total)
           encoded_chunks 0) ^
     " authority=cval-and-source-jet-semantics-proved-analytic-finish-pending");
  List.iter
    (fun (box_name,lower,upper) ->
      candle_dim_jet_scale_run_box_chunked
        case_name box_name encoded_chunks lower upper)
    boxes;;

let candle_dim_jet_scale_run_case_chunked
      case_name monomials negative_constant chunk_width =
  candle_dim_jet_scale_run_case_chunked_on_boxes
    case_name monomials negative_constant chunk_width
    candle_dim_jet_scale_boxes;;

let candle_dim_jet_scale_run_case_on_boxes
      case_name monomials negative_constant boxes =
  candle_dim_jet_scale_marker "prepare" case_name "all" "begin";
  let program = candle_dim_jet_scale_program monomials negative_constant in
  let program_tm = mk_list (program,candle_q_instruction_type) in
  let program_rep = rand (concl (candle_q_program_encode_conv program_tm)) in
  candle_dim_jet_scale_marker "prepare" case_name "all" "end";
  print_endline
    ("CANDLE_DIM_JET_SCALE_PREP case=" ^ case_name ^
     " monomials=" ^ string_of_int (length monomials) ^
     " instructions=" ^ string_of_int (length program) ^
     " encoded_term_chars=" ^
       string_of_int (String.length (string_of_term program_rep)) ^
     " authority=cval-and-source-jet-semantics-proved-analytic-finish-pending");
  List.iter
    (fun (box_name,lower,upper) ->
      candle_dim_jet_scale_run_box
        case_name box_name program_rep lower upper)
    boxes;;

let candle_dim_jet_scale_run_case case_name monomials negative_constant =
  candle_dim_jet_scale_run_case_on_boxes
    case_name monomials negative_constant candle_dim_jet_scale_boxes;;

let candle_dim_jet_scale_first count items =
  fst (chop_list count items);;

let _ =
  candle_dim_jet_scale_run_case
    "quadratic-21" candle_dim_jet_scale_quadratic 128;;

let _ =
  List.iter
    (fun monomial_count ->
      candle_dim_jet_scale_run_case_on_boxes
        ("mixed-prefix-" ^ string_of_int monomial_count)
        (candle_dim_jet_scale_first
          monomial_count candle_dim_jet_scale_mixed)
        512
        [hd candle_dim_jet_scale_boxes])
    [26;31;36;41];;

let _ =
  candle_dim_jet_scale_run_case_chunked
    "mixed-47" candle_dim_jet_scale_mixed 512 128;;

let _ =
  candle_dim_jet_scale_run_case_chunked
    "dense-92" candle_dim_jet_scale_dense 2048 128;;

(* These deliberately synthetic Flyspeck-shaped polynomials contain every   *)
(* repeated monomial in six coordinates through degrees four and five.  They *)
(* exercise every Hessian entry and reuse one encoded expression over three  *)
(* boxes with very different rational-denominator behaviour.                 *)

let _ =
  candle_dim_jet_scale_run_case_chunked
    "degree2-through4-203" candle_dim_jet_scale_degree2_through4 8192 128;;

let _ =
  candle_dim_jet_scale_run_case_chunked
    "degree2-through5-455" candle_dim_jet_scale_degree2_through5 32768 128;;

let _ =
  candle_dim_jet_scale_run_center_profile
    "degree2-through5-455-center-profile"
    candle_dim_jet_scale_degree2_through5 32768 128;;

(* Larger synthetic stress cases retain the same supported expression       *)
(* language and six-coordinate derivative surface.  The degree-six program  *)
(* is reused over all three boxes.  Degree seven uses the two binary boxes:   *)
(* the corresponding prime-denominator stress case is deliberately separate *)
(* because its exact rationals exceed the practical Taylor-handoff boundary. *)

let _ =
  candle_dim_jet_scale_run_case_chunked
    "degree2-through6-917" candle_dim_jet_scale_degree2_through6 131072 128;;

let _ =
  candle_dim_jet_scale_run_case_chunked_on_boxes
    "degree2-through7-1709" candle_dim_jet_scale_degree2_through7 524288 128
    candle_dim_jet_scale_binary_boxes;;

print_endline "CANDLE_CV_POLYNOMIAL_EXPR_DIM_JET_SCALING_OK";;
