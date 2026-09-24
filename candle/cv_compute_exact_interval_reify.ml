(* ========================================================================== *)
(* Strict theorem-producing reification for exact interval programs.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  ML selects a postfix program, but that choice *)
(* has no authority on its own: candle_q_reify_real_expression returns a      *)
(* kernel theorem equating execution of the selected program with the source  *)
(* real expression.  The interval adapter then combines that theorem with     *)
(* reflected evaluation and the generic interval soundness theorem.           *)
(* ========================================================================== *)

needs "candle/compute.ml";;
needs "candle/cv_compute_exact_interval_program.ml";;

module Candle_cv_exact_interval_reify = struct

open Candle_cv_linear_combination_core;;
open Candle_cv_linear_combination_realize;;
open Candle_cv_exact_rational_core;;
open Candle_cv_exact_interval_core;;
open Candle_cv_exact_interval_program;;

let candle_q_reify_zero = Num.num_of_int 0;;
let candle_q_reify_one = Num.num_of_int 1;;
let candle_q_instruction_type = `:candle_q_instruction`;;
let candle_q_interval_type = `:((num#num)#num)#((num#num)#num)`;;

let candle_q_term rational =
  let numerator,denominator = numdom rational in
  if denominator <=/ candle_q_reify_zero then
    failwith "candle_q reifier: nonpositive rational denominator";
  let positive,negative =
    if numerator >=/ candle_q_reify_zero then
      numerator,candle_q_reify_zero
    else candle_q_reify_zero,minus_num numerator in
  mk_pair
    (mk_pair (mk_numeral positive,mk_numeral negative),
     mk_numeral (denominator -/ candle_q_reify_one));;

let candle_q_push_term rational =
  let signed,denominator_predecessor =
    dest_pair (candle_q_term rational) in
  let positive,negative = dest_pair signed in
  list_mk_comb
    (`Candle_q_push`,
     [positive;negative;denominator_predecessor]);;

let candle_q_load_term index =
  mk_comb (`Candle_q_load`,mk_numeral (Num.num_of_int index));;

let candle_q_neg_term = `Candle_q_neg`;;
let candle_q_add_term = `Candle_q_add`;;
let candle_q_mul_term = `Candle_q_mul`;;
let candle_q_square_term = `Candle_q_square`;;

let rec candle_q_variable_index_from index variable = function
  | [] -> None
  | candidate::rest ->
      if aconv variable candidate then Some index
      else candle_q_variable_index_from (index + 1) variable rest;;

let candle_q_variable_index variables variable =
  candle_q_variable_index_from 0 variable variables;;

let candle_q_dest_unary operator tm =
  let actual,arg = dest_comb tm in
  if actual = operator then arg
  else failwith "candle_q reifier: unary operator mismatch";;

let candle_q_dest_binary operator tm =
  let partial,right = dest_comb tm in
  let actual,left = dest_comb partial in
  if actual = operator then left,right
  else failwith "candle_q reifier: binary operator mismatch";;

let candle_q_is_unary operator tm =
  try let _ = candle_q_dest_unary operator tm in true
  with Failure _ -> false;;

let candle_q_is_binary operator tm =
  try let _ = candle_q_dest_binary operator tm in true
  with Failure _ -> false;;

let candle_q_decimal_rational tm =
  let numerator_tm,denominator_tm =
    candle_q_dest_binary `DECIMAL` tm in
  let numerator = dest_numeral numerator_tm and
      denominator = dest_numeral denominator_tm in
  if Num.eq_num denominator (Num.num_of_int 0) then
    failwith "candle_q reifier: zero decimal denominator";
  Num.div_num numerator denominator;;

let rec candle_q_repeat_program base count =
  if count = 0 then [candle_q_push_term (Num.num_of_int 1)]
  else if count = 1 then base
  else if count = 2 then base @ [candle_q_square_term]
  else candle_q_repeat_program base (count - 1) @ base @
       [candle_q_mul_term];;

let rec candle_q_compile_real_expression variables tm =
  match candle_q_variable_index variables tm with
  | Some index -> [candle_q_load_term index]
  | None ->
      if is_ratconst tm then [candle_q_push_term (rat_of_term tm)]
      else if candle_q_is_binary `DECIMAL` tm then
        [candle_q_push_term (candle_q_decimal_rational tm)]
      else if candle_q_is_unary `(--):real->real` tm then
        candle_q_compile_real_expression variables
          (candle_q_dest_unary `(--):real->real` tm) @
        [candle_q_neg_term]
      else if candle_q_is_binary `(+):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(+):real->real->real` tm in
        candle_q_compile_real_expression variables left @
        candle_q_compile_real_expression variables right @
        [candle_q_add_term]
      else if candle_q_is_binary `(-):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(-):real->real->real` tm in
        candle_q_compile_real_expression variables left @
        candle_q_compile_real_expression variables right @
        [candle_q_neg_term; candle_q_add_term]
      else if candle_q_is_binary `(*):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(*):real->real->real` tm in
        candle_q_compile_real_expression variables left @
        candle_q_compile_real_expression variables right @
        [candle_q_mul_term]
      else if candle_q_is_binary `(pow):real->num->real` tm then
        let base,exponent_tm =
          candle_q_dest_binary `(pow):real->num->real` tm in
        let exponent = Num.int_of_num (dest_numeral exponent_tm) in
        if exponent < 0 || exponent > 16 then
          failwith "candle_q reifier: exponent is outside 0..16";
        candle_q_repeat_program
          (candle_q_compile_real_expression variables base) exponent
      else
        failwith "candle_q reifier: unsupported real expression";;

let candle_q_numeral_suc_expansion index =
  if index <= 0 then
    failwith "candle_q reifier: nonpositive numeral expansion";
  let predecessor = mk_numeral (Num.num_of_int (index - 1)) in
  SYM (NUM_SUC_CONV (mk_comb (`SUC`,predecessor)));;

let rec candle_q_numeral_suc_expansions index =
  if index <= 0 then []
  else candle_q_numeral_suc_expansion index::
       candle_q_numeral_suc_expansions (index - 1);;

let candle_q_real_cons_const =
  rator (rator `CONS (&0) ([]:real list)`);;

let candle_q_instruction_append_const =
  rator
    (rator
      `APPEND ([]:candle_q_instruction list)
         ([]:candle_q_instruction list)`);;

let candle_q_append_program left right =
  mk_comb (mk_comb (candle_q_instruction_append_const,left),right);;

let candle_q_component_goal variables program denotation =
  let stack = mk_var ("stack",`:real list`) in
  let run =
    list_mk_comb
      (`candle_q_real_run`,
       [mk_list (variables,`:real`);program;stack]) in
  let result =
    mk_comb (mk_comb (candle_q_real_cons_const,denotation),stack) in
  mk_forall (stack,mk_eq (run,result));;

let candle_q_base_component variables denotation instruction =
  let program = mk_list ([instruction],candle_q_instruction_type) in
  let goal = candle_q_component_goal variables program denotation in
  let index_expansions =
    candle_q_numeral_suc_expansions (length variables) in
  let th = prove
    (goal,
     REWRITE_TAC
       (index_expansions @
        [candle_q_real_run_def; candle_q_real_step_def;
         candle_q_real_lookup_def; candle_q_real_head_def;
         candle_q_real_tail_def; candle_q_real_def; candle_q_den_def;
         candle_lc_zreal_def; REAL_SUB_RZERO; REAL_SUB_LZERO;
         REAL_NEG_0]) THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
     REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RID;
                 REAL_DIV_1]) in
  program,denotation,th;;

let candle_q_rational_component variables source rational =
  let rational_tm = candle_q_term rational in
  let exact_denotation = mk_comb (`candle_q_real`,rational_tm) in
  let program,_,exact_th =
    candle_q_base_component variables exact_denotation
      (candle_q_push_term rational) in
  let denotation_th = prove
    (mk_eq (exact_denotation,source),
     REWRITE_TAC[candle_q_real_def; candle_q_den_def;
                 candle_lc_zreal_def] THEN
     REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
     CONV_TAC REAL_RAT_REDUCE_CONV) in
  program,source,REWRITE_RULE[denotation_th] exact_th;;

let candle_q_unary_component
      variables (program,_,component_th) instruction denotation =
  let suffix = mk_list ([instruction],candle_q_instruction_type) in
  let symbolic_program = candle_q_append_program program suffix in
  let expansion_th = REWRITE_CONV[APPEND] symbolic_program in
  let concrete_program = rand (concl expansion_th) in
  let goal =
    candle_q_component_goal variables concrete_program denotation in
  let th = prove
    (goal,
     GEN_TAC THEN ONCE_REWRITE_TAC[SYM expansion_th] THEN
     REWRITE_TAC[candle_q_real_run_append; component_th;
                 candle_q_real_run_def; candle_q_real_step_def;
                 candle_q_real_head_def; candle_q_real_tail_def;
                 real_sub]) in
  concrete_program,denotation,th;;

let candle_q_binary_component
      variables (left_program,_,left_th) (right_program,_,right_th)
      instruction denotation =
  let suffix = mk_list ([instruction],candle_q_instruction_type) in
  let symbolic_program =
    candle_q_append_program left_program
      (candle_q_append_program right_program suffix) in
  let expansion_th = REWRITE_CONV[APPEND] symbolic_program in
  let concrete_program = rand (concl expansion_th) in
  let goal =
    candle_q_component_goal variables concrete_program denotation in
  let th = prove
    (goal,
     GEN_TAC THEN ONCE_REWRITE_TAC[SYM expansion_th] THEN
     REWRITE_TAC[candle_q_real_run_append; left_th; right_th;
                 candle_q_real_run_def; candle_q_real_step_def;
                 candle_q_real_head_def; candle_q_real_tail_def;
                 real_sub]) in
  concrete_program,denotation,th;;

let rec candle_q_repeat_component variables base count =
  if count = 0 then
    candle_q_rational_component variables `&1` (Num.num_of_int 1)
  else if count = 1 then base
  else if count = 2 then
    let _,base_denotation,_ = base in
    candle_q_unary_component variables base candle_q_square_term
      (mk_binop `(*):real->real->real` base_denotation base_denotation)
  else
    let previous = candle_q_repeat_component variables base (count - 1) in
    let _,previous_denotation,_ = previous in
    let _,base_denotation,_ = base in
    candle_q_binary_component variables previous base candle_q_mul_term
      (mk_binop `(*):real->real->real`
        previous_denotation base_denotation);;

let rec candle_q_compile_proved_expression variables tm =
  match candle_q_variable_index variables tm with
  | Some index ->
      candle_q_base_component variables tm (candle_q_load_term index)
  | None ->
      if is_ratconst tm then
        candle_q_rational_component variables tm (rat_of_term tm)
      else if candle_q_is_binary `DECIMAL` tm then
        let decimal_th = REWRITE_CONV[DECIMAL] tm in
        let normalized_tm = rand (concl decimal_th) in
        let program,_,normalized_th =
          candle_q_rational_component variables normalized_tm
            (candle_q_decimal_rational tm) in
        program,tm,REWRITE_RULE[SYM decimal_th] normalized_th
      else if candle_q_is_unary `(--):real->real` tm then
        let child = candle_q_dest_unary `(--):real->real` tm in
        candle_q_unary_component variables
          (candle_q_compile_proved_expression variables child)
          candle_q_neg_term tm
      else if candle_q_is_binary `(+):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(+):real->real->real` tm in
        candle_q_binary_component variables
          (candle_q_compile_proved_expression variables left)
          (candle_q_compile_proved_expression variables right)
          candle_q_add_term tm
      else if candle_q_is_binary `(-):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(-):real->real->real` tm in
        let negated_right =
          candle_q_unary_component variables
            (candle_q_compile_proved_expression variables right)
            candle_q_neg_term (mk_comb (`(--):real->real`,right)) in
        candle_q_binary_component variables
          (candle_q_compile_proved_expression variables left)
          negated_right candle_q_add_term tm
      else if candle_q_is_binary `(*):real->real->real` tm then
        let left,right =
          candle_q_dest_binary `(*):real->real->real` tm in
        candle_q_binary_component variables
          (candle_q_compile_proved_expression variables left)
          (candle_q_compile_proved_expression variables right)
          candle_q_mul_term tm
      else if candle_q_is_binary `(pow):real->num->real` tm then
        let base_tm,exponent_tm =
          candle_q_dest_binary `(pow):real->num->real` tm in
        let exponent = Num.int_of_num (dest_numeral exponent_tm) in
        if exponent < 0 || exponent > 16 then
          failwith "candle_q reifier: exponent is outside 0..16";
        let program,expanded,expanded_th =
          candle_q_repeat_component variables
            (candle_q_compile_proved_expression variables base_tm)
            exponent in
        let denotation_th = prove
          (mk_eq (expanded,tm),
           REWRITE_TAC
             (candle_q_numeral_suc_expansions exponent @
              [real_pow; REAL_MUL_RID; REAL_MUL_ASSOC]) THEN
           REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
           REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RID]) in
        program,tm,REWRITE_RULE[denotation_th] expanded_th
      else
        failwith "candle_q reifier: unsupported real expression";;

let candle_q_reify_real_expression variables tm =
  if exists (fun variable -> type_of variable <> `:real`) variables then
    failwith "candle_q reifier: non-real variable basis";
  if type_of tm <> `:real` then
    failwith "candle_q reifier: expression is not real";
  let program_tm,denotation,stack_th =
    candle_q_compile_proved_expression variables tm in
  if not (aconv denotation tm) then
    failwith "candle_q reifier: denotation term mismatch";
  let run_th = SPEC `[]:real list` stack_th in
  let expected =
    mk_eq
      (list_mk_comb
        (`candle_q_real_run`,
         [mk_list (variables,`:real`);program_tm;`[]:real list`]),
       mk_list ([tm],`:real`)) in
  if hyp run_th <> [] || not (aconv (concl run_th) expected) then
    failwith "candle_q reifier: kernel reconstruction mismatch";
  program_tm,run_th;;

let candle_q_interval_list_encode_conv intervals_tm =
  REWRITE_CONV
    [candle_cv_q_interval_list_def; candle_cv_q_interval_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_interval_list`,intervals_tm));;

let candle_q_program_encode_conv program_tm =
  REWRITE_CONV
    [candle_cv_q_instruction_list_def; candle_cv_q_instruction_def;
     candle_cv_q_def; candle_cv_lc_z_def]
    (mk_comb (`candle_cv_q_instruction_list`,program_tm));;

let candle_q_interval_list_decode_conv value_tm =
  REWRITE_CONV
    [candle_cv_q_interval_list_decode_def;
     candle_cv_q_interval_decode_def; candle_cv_q_decode_def;
     candle_cv_lc_z_decode_def; candle_cv_lc_num_decode_def]
    (mk_comb (`candle_cv_q_interval_list_decode`,value_tm));;

let candle_q_compute_interval_program
      variables intervals_tm tm program_tm real_run_th =
  let variables_tm = mk_list (variables,`:real`) in
  let expected_real_run =
    mk_eq
      (list_mk_comb
        (`candle_q_real_run`,
         [variables_tm;program_tm;`[]:real list`]),
       mk_list ([tm],`:real`)) in
  if hyp real_run_th <> [] ||
     not (aconv (concl real_run_th) expected_real_run) then
    failwith "candle_q reifier: invalid real execution theorem";
  let interval_rep = candle_q_interval_list_encode_conv intervals_tm in
  let program_rep = candle_q_program_encode_conv program_tm in
  let empty_intervals = mk_list ([],candle_q_interval_type) in
  let empty_rep = candle_q_interval_list_encode_conv empty_intervals in
  let compute_tm =
    list_mk_comb
      (`candle_cv_q_interval_run`,
       [rand (concl interval_rep); rand (concl program_rep);
        rand (concl empty_rep)]) in
  let compute_th =
    compute candle_cv_q_interval_program_compute_eqs compute_tm in
  let representation_th =
    SPECL [program_tm;intervals_tm;empty_intervals]
      candle_cv_q_interval_run_correct in
  let representation_th =
    PURE_REWRITE_RULE [interval_rep;program_rep;empty_rep]
      representation_th in
  if not (aconv (lhand (concl representation_th))
                 (lhand (concl compute_th))) then
    failwith "candle_q reifier: reflected evaluator lhs mismatch";
  let encoded_result_th =
    TRANS (SYM representation_th) compute_th in
  let raw_result = rand (concl compute_th) in
  let raw_decode_th = candle_q_interval_list_decode_conv raw_result in
  let ordinary_result_th =
    REWRITE_RULE
      [candle_cv_q_interval_list_roundtrip; raw_decode_th]
      (AP_TERM `candle_cv_q_interval_list_decode` encoded_result_th) in
  let result_intervals = rand (concl ordinary_result_th) in
  let result_items = dest_list result_intervals in
  if length result_items <> 1 then
    failwith "candle_q reifier: program did not return one interval";
  variables_tm,program_tm,result_intervals,real_run_th,compute_th,
  ordinary_result_th;;

let candle_q_compute_interval_expression variables intervals_tm tm =
  let program_tm,real_run_th =
    candle_q_reify_real_expression variables tm in
  candle_q_compute_interval_program
    variables intervals_tm tm program_tm real_run_th;;

let candle_q_prove_interval_expression
      variables intervals_tm environment_contains_th tm =
  let variables_tm,program_tm,result_intervals,real_run_th,compute_th,
      ordinary_result_th =
    candle_q_compute_interval_expression variables intervals_tm tm in
  let empty_intervals = mk_list ([],candle_q_interval_type) in
  let empty_reals = `[]:real list` in
  let empty_contains_th =
    EQT_ELIM
      (REWRITE_CONV[candle_q_stack_contains_def]
        `candle_q_stack_contains
           ([]:(((num#num)#num)#((num#num)#num))list) ([]:real list)`) in
  let sound_th =
    SPECL
      [program_tm;intervals_tm;variables_tm;empty_intervals;empty_reals]
      candle_q_interval_run_sound in
  let sound_th =
    MP sound_th (CONJ environment_contains_th empty_contains_th) in
  let sound_th =
    REWRITE_RULE
      [ordinary_result_th; real_run_th; candle_q_stack_contains_def]
      sound_th in
  let result_interval = hd (dest_list result_intervals) in
  let expected =
    list_mk_comb (`candle_q_interval_contains`,[result_interval;tm]) in
  if not (aconv (concl sound_th) expected) then
    failwith "candle_q reifier: final interval theorem mismatch";
  result_interval,program_tm,compute_th,sound_th;;

end;;
