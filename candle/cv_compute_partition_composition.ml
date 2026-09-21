(* ========================================================================== *)
(* Generic proof-producing composition for partition certificates.           *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  This theory deliberately abstracts over the   *)
(* domain type, the predicate being proved, and the four domain transformers. *)
(* A client such as Flyspeck instantiates the closure hypotheses with its     *)
(* already-proved bisect/fraction lemmas.  The resulting root theorem remains *)
(* an ordinary kernel theorem; the encoded tree or its ML builder has no      *)
(* authority of its own.                                                      *)
(* ========================================================================== *)

module Candle_cv_partition_composition = struct

let candle_partition_INDUCT,candle_partition_RECURSION = define_type
  "candle_partition =
     Candle_partition_leaf
   | Candle_partition_bisect num candle_partition candle_partition
   | Candle_partition_recurse_left num num num candle_partition
   | Candle_partition_recurse_right num num num candle_partition";;

(* [recurse_left i n q child] records a fractional split whose right domain  *)
(* is an immediate leaf and whose left domain is partitioned by [child].      *)
(* [recurse_right] is its mirror image.  [n]/[q] is kept exact.               *)

let candle_partition_holds_def = define
 `(candle_partition_holds candle_partition_predicate candle_partition_bisect_left
      candle_partition_bisect_right candle_partition_frac_left
      candle_partition_frac_right candle_partition_domain
      Candle_partition_leaf <=>
     candle_partition_predicate candle_partition_domain) /\
  (candle_partition_holds candle_partition_predicate candle_partition_bisect_left
      candle_partition_bisect_right candle_partition_frac_left
      candle_partition_frac_right candle_partition_domain
      (Candle_partition_bisect candle_partition_index
        candle_partition_left_tree candle_partition_right_tree) <=>
     candle_partition_holds candle_partition_predicate candle_partition_bisect_left
       candle_partition_bisect_right candle_partition_frac_left
       candle_partition_frac_right
       (candle_partition_bisect_left candle_partition_index
         candle_partition_domain)
       candle_partition_left_tree /\
     candle_partition_holds candle_partition_predicate candle_partition_bisect_left
       candle_partition_bisect_right candle_partition_frac_left
       candle_partition_frac_right
       (candle_partition_bisect_right candle_partition_index
         candle_partition_domain)
       candle_partition_right_tree) /\
  (candle_partition_holds candle_partition_predicate candle_partition_bisect_left
      candle_partition_bisect_right candle_partition_frac_left
      candle_partition_frac_right candle_partition_domain
      (Candle_partition_recurse_left candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) <=>
     candle_partition_holds candle_partition_predicate candle_partition_bisect_left
       candle_partition_bisect_right candle_partition_frac_left
       candle_partition_frac_right
       (candle_partition_frac_left candle_partition_index
         candle_partition_numerator candle_partition_denominator
         candle_partition_domain)
       candle_partition_child_tree /\
     candle_partition_predicate
       (candle_partition_frac_right candle_partition_index
         candle_partition_numerator candle_partition_denominator
         candle_partition_domain)) /\
  (candle_partition_holds candle_partition_predicate candle_partition_bisect_left
      candle_partition_bisect_right candle_partition_frac_left
      candle_partition_frac_right candle_partition_domain
      (Candle_partition_recurse_right candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) <=>
     candle_partition_predicate
       (candle_partition_frac_left candle_partition_index
         candle_partition_numerator candle_partition_denominator
         candle_partition_domain) /\
     candle_partition_holds candle_partition_predicate candle_partition_bisect_left
       candle_partition_bisect_right candle_partition_frac_left
       candle_partition_frac_right
       (candle_partition_frac_right candle_partition_index
         candle_partition_numerator candle_partition_denominator
         candle_partition_domain)
       candle_partition_child_tree)`;;

let candle_partition_well_formed_def = define
 `(candle_partition_well_formed candle_partition_dimension
      Candle_partition_leaf <=> T) /\
  (candle_partition_well_formed candle_partition_dimension
      (Candle_partition_bisect candle_partition_index
        candle_partition_left_tree candle_partition_right_tree) <=>
     candle_partition_index < candle_partition_dimension /\
     candle_partition_well_formed candle_partition_dimension
       candle_partition_left_tree /\
     candle_partition_well_formed candle_partition_dimension
       candle_partition_right_tree) /\
  (candle_partition_well_formed candle_partition_dimension
      (Candle_partition_recurse_left candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) <=>
     candle_partition_index < candle_partition_dimension /\
     0 < candle_partition_denominator /\
     candle_partition_numerator <= candle_partition_denominator /\
     candle_partition_well_formed candle_partition_dimension
       candle_partition_child_tree) /\
  (candle_partition_well_formed candle_partition_dimension
      (Candle_partition_recurse_right candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) <=>
     candle_partition_index < candle_partition_dimension /\
     0 < candle_partition_denominator /\
     candle_partition_numerator <= candle_partition_denominator /\
     candle_partition_well_formed candle_partition_dimension
       candle_partition_child_tree)`;;

let candle_partition_case_count_def = define
 `(candle_partition_case_count Candle_partition_leaf = 1) /\
  (candle_partition_case_count
      (Candle_partition_bisect candle_partition_index
        candle_partition_left_tree candle_partition_right_tree) =
     candle_partition_case_count candle_partition_left_tree +
     candle_partition_case_count candle_partition_right_tree) /\
  (candle_partition_case_count
      (Candle_partition_recurse_left candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) =
     SUC (candle_partition_case_count candle_partition_child_tree)) /\
  (candle_partition_case_count
      (Candle_partition_recurse_right candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) =
     SUC (candle_partition_case_count candle_partition_child_tree))`;;

let candle_partition_leaf_count_def = define
 `(candle_partition_leaf_count Candle_partition_leaf = 1) /\
  (candle_partition_leaf_count
      (Candle_partition_bisect candle_partition_index
        candle_partition_left_tree candle_partition_right_tree) =
     candle_partition_leaf_count candle_partition_left_tree +
     candle_partition_leaf_count candle_partition_right_tree) /\
  (candle_partition_leaf_count
      (Candle_partition_recurse_left candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) =
     candle_partition_leaf_count candle_partition_child_tree) /\
  (candle_partition_leaf_count
      (Candle_partition_recurse_right candle_partition_index
        candle_partition_numerator candle_partition_denominator
        candle_partition_child_tree) =
     candle_partition_leaf_count candle_partition_child_tree)`;;

let candle_partition_composition_sound = prove
 (`!p candle_partition_bisect_left candle_partition_bisect_right
      candle_partition_frac_left candle_partition_frac_right.
     (!i d. p (candle_partition_bisect_left i d) /\
       p (candle_partition_bisect_right i d) ==> p d) /\
     (!i n q d. p (candle_partition_frac_left i n q d) /\
       p (candle_partition_frac_right i n q d) ==> p d)
     ==> !tree d.
       candle_partition_holds
         p candle_partition_bisect_left candle_partition_bisect_right
         candle_partition_frac_left candle_partition_frac_right d tree
       ==> p d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_partition_INDUCT THEN
  REWRITE_TAC[candle_partition_holds_def] THEN
  ASM_MESON_TAC[]);;

(* Most real clients have a structural invariant that is not repeated in    *)
(* every imported leaf theorem.  In Flyspeck it is [LENGTH x = LENGTH d].    *)
(* This variant propagates that invariant through the tree while keeping     *)
(* [candle_partition_holds] exactly the conjunction of analytic leaf facts.  *)

let candle_partition_composition_sound_with_invariant = prove
 (`!invariant p candle_partition_bisect_left candle_partition_bisect_right
      candle_partition_frac_left candle_partition_frac_right.
     (!i d. invariant d ==>
       invariant (candle_partition_bisect_left i d) /\
       invariant (candle_partition_bisect_right i d)) /\
     (!i n q d. invariant d ==>
       invariant (candle_partition_frac_left i n q d) /\
       invariant (candle_partition_frac_right i n q d)) /\
     (!i d. invariant d ==>
       p (candle_partition_bisect_left i d) /\
       p (candle_partition_bisect_right i d) ==> p d) /\
     (!i n q d. invariant d ==>
       p (candle_partition_frac_left i n q d) /\
       p (candle_partition_frac_right i n q d) ==> p d)
     ==> !tree d.
       invariant d /\
       candle_partition_holds
         p candle_partition_bisect_left candle_partition_bisect_right
         candle_partition_frac_left candle_partition_frac_right d tree
       ==> p d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_partition_INDUCT THEN
  REWRITE_TAC[candle_partition_holds_def] THEN
  ASM_MESON_TAC[]);;

end;;
