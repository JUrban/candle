(* A fresh-base, theorem-producing regression for the verified compute
   primitive.  Kernel.compute accepts COMPUTE_INIT_THMS only when the complete
   ordered list is exactly CakeML's compiled compute_thms value, so every
   successful call below is also an exact whole-contract comparison. *)

needs "candle/compute.ml";;

let compute_contract_assert label condition =
  if condition then print_endline ("CANDLE_COMPUTE_OK:" ^ label)
  else failwith ("Candle compute contract regression: " ^ label);;

let compute_contract_conclusion label expected theorem =
  compute_contract_assert label
    (hyp theorem = [] && aconv (concl theorem) expected);;

compute_contract_assert "init_theorem_count"
  (length COMPUTE_INIT_THMS = 62);;

let compute_arithmetic_thm = compute []
  `Cexp_add (Cexp_num 123) (Cexp_num 456)`;;
compute_contract_conclusion "arithmetic"
  `Cexp_add (Cexp_num 123) (Cexp_num 456) = Cexp_num 579`
  compute_arithmetic_thm;;

let compute_div_mod_thm = compute []
  `Cexp_pair
     (Cexp_div (Cexp_num 123) (Cexp_num 10))
     (Cexp_mod (Cexp_num 123) (Cexp_num 10))`;;
compute_contract_conclusion "div_mod_pair"
  `Cexp_pair
     (Cexp_div (Cexp_num 123) (Cexp_num 10))
     (Cexp_mod (Cexp_num 123) (Cexp_num 10)) =
   Cexp_pair (Cexp_num 12) (Cexp_num 3)`
  compute_div_mod_thm;;

let compute_num_if_thm = compute []
  `Cexp_if (Cexp_num 1) (Cexp_num 7) (Cexp_num 9)`;;
compute_contract_conclusion "numeric_if"
  `Cexp_if (Cexp_num 1) (Cexp_num 7) (Cexp_num 9) = Cexp_num 7`
  compute_num_if_thm;;

let compute_pair_if_thm = compute []
  `Cexp_if (Cexp_pair (Cexp_num 1) (Cexp_num 2))
           (Cexp_num 7) (Cexp_num 9)`;;
compute_contract_conclusion "pair_if_uses_else_branch"
  `Cexp_if (Cexp_pair (Cexp_num 1) (Cexp_num 2))
           (Cexp_num 7) (Cexp_num 9) = Cexp_num 9`
  compute_pair_if_thm;;

let compute_nested_eq_thm = compute []
  `Cexp_eq
     (Cexp_pair (Cexp_num 5) (Cexp_pair (Cexp_num 8) (Cexp_num 13)))
     (Cexp_pair (Cexp_num 5) (Cexp_pair (Cexp_num 8) (Cexp_num 13)))`;;
compute_contract_conclusion "nested_pair_equality"
  `Cexp_eq
     (Cexp_pair (Cexp_num 5) (Cexp_pair (Cexp_num 8) (Cexp_num 13)))
     (Cexp_pair (Cexp_num 5) (Cexp_pair (Cexp_num 8) (Cexp_num 13))) =
   Cexp_num 1`
  compute_nested_eq_thm;;

let compute_contract_double_def = new_definition
  `compute_contract_double x = Cexp_add x x`;;
let compute_user_equation_thm = compute [SPEC_ALL compute_contract_double_def]
  `compute_contract_double (Cexp_num 21)`;;
compute_contract_conclusion "user_equation_theorem_handoff"
  `compute_contract_double (Cexp_num 21) = Cexp_num 42`
  compute_user_equation_thm;;

let compute_contract_rejected init_thms =
  try
    let _ = Kernel.compute (init_thms, []) `Cexp_num 0` in false
  with Failure _ -> true;;

let compute_contract_swapped =
  match COMPUTE_INIT_THMS with
  | first :: second :: rest -> second :: first :: rest
  | _ -> failwith "Candle compute initialization contract is unexpectedly short";;

compute_contract_assert "swapped_contract_rejected"
  (compute_contract_rejected compute_contract_swapped);;
compute_contract_assert "short_contract_rejected"
  (compute_contract_rejected (tl COMPUTE_INIT_THMS));;

print_endline "CANDLE_COMPUTE_CONTRACT_OK";;
