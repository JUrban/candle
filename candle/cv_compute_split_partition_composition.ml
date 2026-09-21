(* ========================================================================== *)
(* Generic proof-producing composition for exact binary split certificates.   *)
(*                                                                            *)
(* DEVELOPMENT / NON-RELEASE.  A node retains both its coordinate and exact   *)
(* real split value.  Clients prove one closure theorem for their domain      *)
(* transformers; the encoded tree and its ML producer carry no proof          *)
(* authority.                                                                  *)
(* ========================================================================== *)

module Candle_cv_split_partition_composition = struct

let candle_split_partition_INDUCT,candle_split_partition_RECURSION =
  define_type
    "candle_split_partition =
       Candle_split_partition_leaf
     | Candle_split_partition_node num real candle_split_partition
         candle_split_partition";;

let candle_split_partition_holds_def = define
 `(candle_split_partition_holds candle_split_predicate
      candle_split_left candle_split_right candle_split_domain
      Candle_split_partition_leaf <=>
     candle_split_predicate candle_split_domain) /\
  (candle_split_partition_holds candle_split_predicate
      candle_split_left candle_split_right candle_split_domain
      (Candle_split_partition_node candle_split_index candle_split_value
        candle_split_left_tree candle_split_right_tree) <=>
     candle_split_partition_holds candle_split_predicate
       candle_split_left candle_split_right
       (candle_split_left candle_split_index candle_split_value
         candle_split_domain)
       candle_split_left_tree /\
     candle_split_partition_holds candle_split_predicate
       candle_split_left candle_split_right
       (candle_split_right candle_split_index candle_split_value
         candle_split_domain)
       candle_split_right_tree)`;;

let candle_split_partition_node_count_def = define
 `(candle_split_partition_node_count Candle_split_partition_leaf = 1) /\
  (candle_split_partition_node_count
      (Candle_split_partition_node candle_split_index candle_split_value
        candle_split_left_tree candle_split_right_tree) =
     1 + candle_split_partition_node_count candle_split_left_tree +
       candle_split_partition_node_count candle_split_right_tree)`;;

let candle_split_partition_leaf_count_def = define
 `(candle_split_partition_leaf_count Candle_split_partition_leaf = 1) /\
  (candle_split_partition_leaf_count
      (Candle_split_partition_node candle_split_index candle_split_value
        candle_split_left_tree candle_split_right_tree) =
     candle_split_partition_leaf_count candle_split_left_tree +
       candle_split_partition_leaf_count candle_split_right_tree)`;;

let candle_split_partition_composition_sound = prove
 (`!candle_split_predicate candle_split_left candle_split_right.
     (!candle_split_index candle_split_value candle_split_domain.
       candle_split_predicate
         (candle_split_left candle_split_index candle_split_value
           candle_split_domain) /\
       candle_split_predicate
         (candle_split_right candle_split_index candle_split_value
           candle_split_domain)
       ==> candle_split_predicate candle_split_domain)
     ==> !candle_split_tree candle_split_domain.
       candle_split_partition_holds candle_split_predicate
         candle_split_left candle_split_right candle_split_domain
         candle_split_tree
       ==> candle_split_predicate candle_split_domain`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC candle_split_partition_INDUCT THEN
  REWRITE_TAC[candle_split_partition_holds_def] THEN
  ASM_MESON_TAC[]);;

end;;

