(* Explicit term ordering for Flyspeck's m_cell_list_pass merge tactic. *)

needs "candle/cv_compute_flyspeck_direct_source_compat.ml";;

module Candle_cv_flyspeck_nonlinear_term_order_compat = struct

open M_taylor;;
open M_verifier;;

(* This is the source tactic from verifier/m_verifier.hl with its one native
   polymorphic term comparison made explicit.  Term.compare is Candle's
   faithful total ordering for HOL terms and is already used by the direct
   source compatibility layer for the same OCaml comparison contract. *)
let candle_nonlinear_merge_m_cell_list_pass n pass_th =
  let append_tm,dom_tm = dest_m_cell_pass (concl pass_th) in
  let list_ty = type_of append_tm in
  let dom_var = mk_var ("domain",type_of dom_tm) and
      fs1_var = mk_var ("fs1",list_ty) and
      fs2_var = mk_var ("fs2",list_ty) and
      acc_var = mk_var ("acc",list_ty) and
      h_var = mk_var ("h",(hd o snd o dest_type) list_ty) in
  let acc_intro,acc_elim,acc_rev,pass_nil1,pass_nil2,same_hd,
      pass_move1,pass_move2 =
    let r = inst_first_type_var n_type_array.(n) in
    r CELL_LIST_PASS_ACC_INTRO,
    r CELL_LIST_PASS_ACC_ELIM,
    r CELL_LIST_PASS_ACC_REV,
    r CELL_LIST_PASS_NIL1,
    r CELL_LIST_PASS_NIL2,
    r CELL_LIST_PASS_SAME_HD,
    r CELL_LIST_PASS_MOVE1,
    r CELL_LIST_PASS_MOVE2 in
  let rec rev_acc th =
    let ltm,s_tm = (dest_comb o rand o rator o concl) th in
    let acc_tm = rand ltm in
    if is_comb s_tm then
      let h_tm,fs2_tm = dest_binary "CONS" s_tm in
      let th1 =
        INST
          [h_tm,h_var;fs2_tm,fs2_var;acc_tm,acc_var;dom_tm,dom_var]
          acc_rev in
      rev_acc (EQ_MP th1 th)
    else
      let th1 = INST [acc_tm,fs1_var;dom_tm,dom_var] acc_elim in
      EQ_MP th1 th in
  let rec merge_append th =
    let ltm,acc_tm = (dest_comb o rand o rator o concl) th in
    let fs1_tm,fs2_tm = dest_binary "APPEND" (rand ltm) in
    if not (is_comb fs1_tm) then
      let th1 =
        INST
          [fs2_tm,fs2_var;acc_tm,acc_var;dom_tm,dom_var]
          pass_nil1 in
      EQ_MP th1 th
    else if not (is_comb fs2_tm) then
      let th1 =
        INST
          [fs1_tm,fs1_var;acc_tm,acc_var;dom_tm,dom_var]
          pass_nil2 in
      EQ_MP th1 th
    else
      let h1_tm,t1_tm = dest_binary "CONS" fs1_tm and
          h2_tm,t2_tm = dest_binary "CONS" fs2_tm in
      let th1 =
        match Term.compare h1_tm h2_tm with
        | -1 ->
            INST
              [h1_tm,h_var;t1_tm,fs1_var;fs2_tm,fs2_var;
               acc_tm,acc_var;dom_tm,dom_var]
              pass_move1
        | 1 ->
            INST
              [h2_tm,h_var;t2_tm,fs2_var;fs1_tm,fs1_var;
               acc_tm,acc_var;dom_tm,dom_var]
              pass_move2
        | _ ->
            INST
              [h1_tm,h_var;t1_tm,fs1_var;t2_tm,fs2_var;
               acc_tm,acc_var;dom_tm,dom_var]
              same_hd in
      merge_append (EQ_MP th1 th) in
  let th0 =
    EQ_MP
      (INST [append_tm,fs1_var;dom_tm,dom_var] acc_intro)
      pass_th in
  rev_acc (merge_append th0);;

print_endline
  "CANDLE_CV_NONLINEAR_TERM_ORDER_COMPAT_OK DEVELOPMENT_NON_RELEASE";;

end;;
