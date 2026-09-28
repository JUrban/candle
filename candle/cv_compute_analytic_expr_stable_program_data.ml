(* ========================================================================== *)
(* Untrusted data preparation for stable reflected analytic programs.         *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  An authenticated analytic program has a fixed *)
(* instruction skeleton.  Different boxes need different square-root interval *)
(* certificates, but they must not be able to alter that skeleton.  These ML  *)
(* helpers encode exact rational data and replace only tag-1 square-root       *)
(* payloads.  They prove nothing: the reflected checker must validate all data *)
(* before a result can contribute to a theorem.                               *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_program_compute.ml";;

module Candle_cv_analytic_expr_stable_program_data = struct

type candle_q_dim_stable_program_patch = {
  stable_program_patch_term : term;
  stable_program_patch_sqrt_slots : int;
};;

let candle_q_dim_stable_program_cval_pair left right =
  list_mk_comb (`Cexp_pair`,[left;right]);;

let candle_q_dim_stable_program_cval_num numeral =
  let _ = dest_numeral numeral in
  mk_comb (`Cexp_num`,numeral);;

let candle_q_dim_stable_program_dest_cval_pair context tm =
  let operator,arguments = strip_comb tm in
  if aconv operator `Cexp_pair` then
    match arguments with
    | [left;right] -> left,right
    | _ -> failwith (context ^ ": malformed Cexp_pair")
  else
    failwith (context ^ ": expected Cexp_pair");;

let candle_q_dim_stable_program_encode_signed signed =
  let positive,negative = dest_pair signed in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_cval_num positive)
    (candle_q_dim_stable_program_cval_num negative);;

let candle_q_dim_stable_program_encode_rational rational =
  let signed,denominator_predecessor = dest_pair rational in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_signed signed)
    (candle_q_dim_stable_program_cval_num denominator_predecessor);;

let candle_q_dim_stable_program_encode_interval interval =
  let lower,upper = dest_pair interval in
  candle_q_dim_stable_program_cval_pair
    (candle_q_dim_stable_program_encode_rational lower)
    (candle_q_dim_stable_program_encode_rational upper);;

let candle_q_dim_stable_program_cval_list items =
  itlist candle_q_dim_stable_program_cval_pair items `Cexp_num 0`;;

let candle_q_dim_stable_program_encode_intervals intervals =
  candle_q_dim_stable_program_cval_list
    (map candle_q_dim_stable_program_encode_interval intervals);;

let candle_q_dim_stable_program_is_sqrt_instruction instruction =
  try
    let tag,_ =
      candle_q_dim_stable_program_dest_cval_pair
        "stable analytic program instruction" instruction in
    aconv tag `Cexp_num 1`
  with Failure _ -> false;;

let candle_q_dim_stable_program_patch_sqrt_intervals intervals program =
  let rec patch remaining current =
    if aconv current `Cexp_num 0` then
      if remaining = [] then current,[],0
      else failwith "stable analytic program: unused square-root intervals"
    else
      let instruction,tail =
        candle_q_dim_stable_program_dest_cval_pair
          "stable analytic program list" current in
      let replacement,after_instruction,local_count =
        if candle_q_dim_stable_program_is_sqrt_instruction instruction then
          match remaining with
          | interval :: rest ->
              candle_q_dim_stable_program_cval_pair
                `Cexp_num 1`
                (candle_q_dim_stable_program_encode_interval interval),
              rest,1
          | [] ->
              failwith "stable analytic program: missing square-root interval"
        else instruction,remaining,0 in
      let patched_tail,after_tail,tail_count =
        patch after_instruction tail in
      candle_q_dim_stable_program_cval_pair replacement patched_tail,
      after_tail,local_count + tail_count in
  let patched,remaining,count = patch intervals program in
  if remaining <> [] then
    failwith "stable analytic program: unused square-root intervals";
  {stable_program_patch_term = patched;
   stable_program_patch_sqrt_slots = count};;

end;;
