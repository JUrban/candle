(* Kernel.compute representation smoke test for the authentic AFP p=0 seed. *)

needs "candle/cv_compute_tame_graph_enumerator_core.ml";;

open Candle_cv_tame_graph_enumerator_core;;

let candle_cv_tame_seed_axioms_before = axioms ();;

let candle_cv_tame_p0_vertices =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 1)
    (Cexp_pair (Cexp_num 2) (Cexp_num 0)))`;;

let candle_cv_tame_p0_reverse_vertices =
 `Cexp_pair (Cexp_num 2)
   (Cexp_pair (Cexp_num 1)
    (Cexp_pair (Cexp_num 0) (Cexp_num 0)))`;;

let candle_cv_tame_p0_final_face =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_vertices),`Cexp_num 1`);;

let candle_cv_tame_p0_open_face =
  mk_comb
    (mk_comb (`Cexp_pair`,candle_cv_tame_p0_reverse_vertices),`Cexp_num 0`);;

let candle_cv_tame_p0_faces =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_final_face),
    mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_open_face),`Cexp_num 0`));;

let candle_cv_tame_p0_faces_at =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_faces),
    mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_faces),
      mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_faces),`Cexp_num 0`)));;

let candle_cv_tame_p0_heights =
 `Cexp_pair (Cexp_num 0)
   (Cexp_pair (Cexp_num 0)
    (Cexp_pair (Cexp_num 0) (Cexp_num 0)))`;;

let candle_cv_tame_p0_expected =
  mk_comb (mk_comb (`Cexp_pair`,candle_cv_tame_p0_faces),
    mk_comb (mk_comb (`Cexp_pair`,`Cexp_num 3`),
      mk_comb
        (mk_comb (`Cexp_pair`,candle_cv_tame_p0_faces_at),
         candle_cv_tame_p0_heights)));;

let candle_cv_tame_three_as_successors = prove
 (`3 = SUC (SUC (SUC 0))`,
  ARITH_TAC);;

let candle_cv_tame_two_as_successors = prove
 (`2 = SUC (SUC 0)`,
  ARITH_TAC);;

let candle_cv_tame_one_as_successor = prove
 (`1 = SUC 0`,
  ARITH_TAC);;

let candle_cv_tame_p0_seed_expanded_theorem =
  REWRITE_CONV
    ([candle_cv_tame_seed_def;
      LET_DEF;
      LET_END_DEF;
      candle_cv_tame_false_def;
      candle_cv_tame_true_def;
      candle_cv_tame_face_def;
      candle_cv_tame_graph_def;
      candle_cv_tame_list_upt_def;
      candle_cv_tame_list_reverse_def;
      ] @
     CONJUNCTS candle_cv_tame_list_upt_count_def @
     CONJUNCTS candle_cv_tame_list_upt_num_def @
     CONJUNCTS candle_cv_tame_list_reverse_aux_def @
     CONJUNCTS candle_cv_tame_list_replicate_def @
     CONJUNCTS candle_cv_tame_list_replicate_num_def @
     CONJUNCTS cexp_add_def @ CONJUNCTS cexp_sub_def @
     [ADD_CLAUSES; SUB_0; candle_cv_tame_three_as_successors])
    `candle_cv_tame_seed (Cexp_num 0)`;;

let candle_cv_tame_p0_seed_theorem =
  CONV_RULE
    (RAND_CONV
      (REWRITE_CONV
        [GSYM candle_cv_tame_three_as_successors;
         GSYM candle_cv_tame_two_as_successors;
         GSYM candle_cv_tame_one_as_successor]))
    candle_cv_tame_p0_seed_expanded_theorem;;

if not
 (aconv (rand (concl candle_cv_tame_p0_seed_theorem))
        candle_cv_tame_p0_expected) then
  failwith "tame enumerator seed: p=0 representation mismatch";;

let candle_cv_tame_p0_min_vertex_theorem =
  candle_cv_tame_enumerator_compute
    (mk_comb
      (mk_comb
        (`candle_cv_tame_min_vertex`,candle_cv_tame_p0_expected),
       mk_comb
        (`candle_cv_tame_face_vertices`,
         mk_comb
          (`candle_cv_tame_min_face`,
           mk_comb
            (`candle_cv_tame_graph_nonfinals`,
             candle_cv_tame_p0_expected)))));;

if not (aconv (rand (concl candle_cv_tame_p0_min_vertex_theorem))
              `Cexp_num 2`) then
  failwith "tame enumerator seed: authentic minimal vertex mismatch";;

let candle_cv_tame_seed_axioms_after = axioms ();;

if length candle_cv_tame_seed_axioms_after <>
     length candle_cv_tame_seed_axioms_before ||
   not (List.for_all
     (fun theorem -> List.mem theorem candle_cv_tame_seed_axioms_before)
     candle_cv_tame_seed_axioms_after) then
  failwith "tame enumerator seed: changed the global axiom set";;

let _ = print_endline
  "CANDLE_CV_TAME_GRAPH_ENUMERATOR_SEED_TEST_OK p=0_min_vertex=2 axiom_growth=0 DEVELOPMENT_NON_RELEASE";;
