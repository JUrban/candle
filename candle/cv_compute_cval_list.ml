(* ========================================================================== *)
(* Small compute-only helpers for cval-encoded lists.                         *)
(*                                                                            *)
(* Keeping this primitive outside the whole-box proof layer lets other       *)
(* reflected checkers load their executable equations without loading the    *)
(* complete Taylor arithmetic and representation theory.                     *)
(* ========================================================================== *)

needs "candle/cv_compute_analytic_expr_program_compute.ml";;

module Candle_cv_cval_list = struct

open Candle_cv_analytic_expr_program_compute;;

let candle_cv_list_length_def = define
 `(candle_cv_list_length (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_list_length (Cexp_pair h t) =
     Cexp_add (Cexp_num 1) (candle_cv_list_length t))`;;

let candle_cv_list_length_compute = prove
 (`!items.
     candle_cv_list_length items =
     Cexp_if (Cexp_ispair items)
       (Cexp_add (Cexp_num 1)
         (candle_cv_list_length (Cexp_snd items)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `items:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_list_length_def;
              cexp_if_def;cexp_ispair_def;cexp_snd_def]);;

print_endline "CANDLE_CV_CVAL_LIST_OK DEVELOPMENT_NON_RELEASE";;

end;;
