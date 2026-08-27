(* Direct-source S3 target glue, loaded only after the complete pinned
   Flyspeck full sequence. *)

module Candle_flyspeck_l2 = struct

let tame_imp_kepler_conjecture =
  let tame = `import_tame_classification` in
  DISCH tame
    (MATCH_MP
      The_kepler_conjecture.tame_nonlinear_imp_kepler_conjecture
      (CONJ (ASSUME tame) Mk_all_ineq.the_nonlinear_inequalities));;

end;;
