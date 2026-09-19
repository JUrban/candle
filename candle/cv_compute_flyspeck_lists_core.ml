(* ========================================================================== *)
(* First-order cval representations/programs for the Flyspeck hypermap lists. *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  Load after candle/compute.ml.  This core has no *)
(* dependency on Flyspeck definitions; flyspeck_cv_compute.ml proves the       *)
(* application-specific bridge and exports the ordinary theorem conversion.   *)
(* ========================================================================== *)

module Candle_cv_flyspeck_lists_core = struct

(* Natural numbers, pairs of naturals, lists, and nested lists.  Cexp_num 0 is *)
(* the list terminator and Cexp_pair is the cons cell.  Type discipline comes *)
(* from the representation theorems, not from an unchecked ML assertion.      *)

let candle_cv_num_list_def = define
 `(candle_cv_num_list ([]:num list) = Cexp_num 0) /\
  (candle_cv_num_list (CONS h t) =
     Cexp_pair (Cexp_num h) (candle_cv_num_list t))`;;

let candle_cv_num_lists_def = define
 `(candle_cv_num_lists ([]:(num list)list) = Cexp_num 0) /\
  (candle_cv_num_lists (CONS h t) =
     Cexp_pair (candle_cv_num_list h) (candle_cv_num_lists t))`;;

let candle_cv_num_decode_def = define
 `(candle_cv_num_decode (Cexp_num n) = n) /\
  (candle_cv_num_decode (Cexp_pair x y) = 0)`;;

let candle_cv_num_pair_decode_def = define
 `(candle_cv_num_pair_decode (Cexp_num n) = (0,0)) /\
  (candle_cv_num_pair_decode (Cexp_pair x y) =
     (candle_cv_num_decode x,candle_cv_num_decode y))`;;

let candle_cv_num_pair_list_def = define
 `(candle_cv_num_pair_list ([]:(num#num)list) = Cexp_num 0) /\
  (candle_cv_num_pair_list (CONS h t) =
     Cexp_pair
       (Cexp_pair (Cexp_num (FST h)) (Cexp_num (SND h)))
       (candle_cv_num_pair_list t))`;;

let candle_cv_num_pair_lists_def = define
 `(candle_cv_num_pair_lists ([]:((num#num)list)list) = Cexp_num 0) /\
  (candle_cv_num_pair_lists (CONS h t) =
     Cexp_pair (candle_cv_num_pair_list h)
               (candle_cv_num_pair_lists t))`;;

let candle_cv_num_pair_list_decode_def = define
 `(candle_cv_num_pair_list_decode (Cexp_num n) = []) /\
  (candle_cv_num_pair_list_decode (Cexp_pair h t) =
     CONS (candle_cv_num_pair_decode h)
          (candle_cv_num_pair_list_decode t))`;;

let candle_cv_num_pair_lists_decode_def = define
 `(candle_cv_num_pair_lists_decode (Cexp_num n) = []) /\
  (candle_cv_num_pair_lists_decode (Cexp_pair h t) =
     CONS (candle_cv_num_pair_list_decode h)
          (candle_cv_num_pair_lists_decode t))`;;

let candle_cv_num_pair_list_roundtrip = prove
 (`!l:(num#num)list.
     candle_cv_num_pair_list_decode (candle_cv_num_pair_list l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_pair_list_def;
                  candle_cv_num_pair_list_decode_def;
                  candle_cv_num_pair_decode_def;
                  candle_cv_num_decode_def]);;

let candle_cv_num_pair_lists_roundtrip = prove
 (`!l:((num#num)list)list.
     candle_cv_num_pair_lists_decode (candle_cv_num_pair_lists l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[candle_cv_num_pair_lists_def;
                  candle_cv_num_pair_lists_decode_def;
                  candle_cv_num_pair_list_roundtrip]);;

(* The constructor equations make the recursive definitions easy to prove.   *)
(* The all-variable equations below are the only equations passed to compute. *)

let candle_cv_list_pairs_aux_def = define
 `(candle_cv_list_pairs_aux hd (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_list_pairs_aux hd (Cexp_pair h t) =
     Cexp_pair
       (Cexp_pair h
         (Cexp_if (Cexp_ispair t) (Cexp_fst t) hd))
       (candle_cv_list_pairs_aux hd t))`;;

let candle_cv_list_pairs_def = new_definition
 `candle_cv_list_pairs x =
    Cexp_if (Cexp_ispair x)
      (candle_cv_list_pairs_aux (Cexp_fst x) x)
      (Cexp_num 0)`;;

let candle_cv_list_of_faces_def = define
 `(candle_cv_list_of_faces (Cexp_num n) = Cexp_num 0) /\
  (candle_cv_list_of_faces (Cexp_pair h t) =
     Cexp_pair (candle_cv_list_pairs h)
               (candle_cv_list_of_faces t))`;;

let candle_cv_list_pairs_aux_compute = prove
 (`!hd x. candle_cv_list_pairs_aux hd x =
     Cexp_if (Cexp_ispair x)
       (Cexp_pair
         (Cexp_pair (Cexp_fst x)
           (Cexp_if (Cexp_ispair (Cexp_snd x))
             (Cexp_fst (Cexp_snd x)) hd))
         (candle_cv_list_pairs_aux hd (Cexp_snd x)))
       (Cexp_num 0)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `x:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_list_pairs_aux_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_list_pairs_compute = SPEC_ALL candle_cv_list_pairs_def;;

let candle_cv_list_of_faces_compute = prove
 (`!x. candle_cv_list_of_faces x =
     Cexp_if (Cexp_ispair x)
       (Cexp_pair (candle_cv_list_pairs (Cexp_fst x))
                  (candle_cv_list_of_faces (Cexp_snd x)))
       (Cexp_num 0)`,
  GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `x:cval` (cases "cval")) THEN
  REWRITE_TAC[candle_cv_list_of_faces_def; cexp_if_def;
              cexp_fst_def; cexp_snd_def; cexp_ispair_def]);;

let candle_cv_list_of_faces_compute_eqs =
  map SPEC_ALL
   [candle_cv_list_pairs_aux_compute;
    candle_cv_list_pairs_compute;
    candle_cv_list_of_faces_compute];;

end;;
