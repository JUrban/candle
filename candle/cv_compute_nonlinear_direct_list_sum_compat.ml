(* ========================================================================== *)
(* Reuse the direct Flyspeck [list_sum] constant in the nonlinear verifier.  *)
(*                                                                            *)
(* The direct source plan has already loaded Seq2.list_sum.  The later        *)
(* Formal_ineqs list_float source gives the same constant an ITLIST contract. *)
(* Prove that contract from the existing definition instead of attempting a  *)
(* second logical constant definition.                                       *)
(* ========================================================================== *)

let candle_cv_direct_foldr_as_itlist = prove
 (`!f z (list:A list). foldr f z list = ITLIST f list z`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[Seq.foldr; ITLIST]);;

let candle_cv_direct_list_sum_as_itlist = prove
 (`!list f. list_sum list f =
             ITLIST (\t1 t2. f t1 + t2) list (&0)`,
  REWRITE_TAC[Seq2.list_sum; candle_cv_direct_foldr_as_itlist]);;

