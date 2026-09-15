# Direct boundary 05: action 153 GLPK-link compatibility

Status: DEVELOPMENT / NON-RELEASE candidate. The first genuine action-153
failure is reproduced and the narrow formatting contract has passed its
native/Candle oracle, but the complete normalized source has not yet passed on
the rebuilt frontend. The cumulative metric therefore remains 152/152 actions,
indices 000--151; neither action 152 nor action 153 receives cumulative credit
from this work.

## First failure

A fresh reflink copy of the immutable focused post-action-152 checkpoint loaded
the exact raw action-153 source, `formal_lp/glpk/glpk_link.ml`. Candle rejected
the top-level alias at source line 33 (reported as diagnostic line 34):

```text
ERROR: Undefined variable: Printf.sprintf at line 34
```

`Glpk_link.convert_to_list` was consequently unbound. The apparent process
exit status is not acceptance because the REPL reports source errors without a
nonzero process exit. The preserved diagnostic attempt is:

```text
/project/flyspeck-candle-runs/v101-focused-action153-raw-dev-001
```

Its input has SHA-256
`cdd1019db44db9e637579699eb61a663b39bbffa90dbbc75b20aa55409078574`
and its log has SHA-256
`cbbf1f462d16373763974a447d2b032f58691fc581ea590b4cbf0d303616b01a`.
The checkpoint copy has the unchanged focused-image identity
`303f4e18e601c50f12515cc346a8dfbb279fb72443b079d27cf1d069543e5e12`.

## Historical check and candidate

The Candle `fix-top100` branch has no Flyspeck source repair for this file.
Inspected Flyspeck develop/native history retains `Printf.sprintf`; unrelated
historical changes do not supply a compatibility solution. The candidate is
therefore one exact hash-pinned replacement of the alias:

```ocaml
let sprintf _ =
  failwith "Candle Flyspeck: non-verification GLPK formatter is disabled";;
```

The exported name is deliberately retained. Both `Glpk_link` and the later
`Lpproc` module contain differently typed and differently curried uses inside
deferred generator/process functions. The replacement infers `'a -> 'b`, so
each definition type-checks through a fresh polymorphic instantiation, while
every attempted invocation fails immediately. It is not a partial formatter,
a basename alias, or authorization for process execution.

The manifest route audit records these calls as belonging to the unused
non-verification GLPK generator/process lane. Any selected caller, any need for
formatted output, or any source drift invalidates this normalization. The
normalized file is 8,077 bytes, SHA-256
`6ffd1be47aa9039f41758794869d77484fe7ee85d4e304a9b944af3d3e3a2d45`,
and MD5 `7034cd37bfda474171f5135efaf73a62`.

The fail-closed oracle exercises integer, string, float, and mixed-arity call
shapes under native OCaml and the current compiled Candle. It confirms the
polymorphic binding and the exact deterministic failure at every call. The
normalization contract and complete manifest have reached a fixed point at 80
entries (79 selected overlays), contract SHA-256
`8e35902c2c43bfa4d4f5a2ec5bbb2e7b0fe8cc84e7eebbb233d6534a56f1475d`,
297 roots, 400 source nodes, and 43 generated inputs.

## Remaining acceptance

The unchanged source also contains an ascending `for` loop and a standalone
module-structure expression. Those constructs are covered centrally by the
isolated CakeML frontend commits `8dc5e5d9618d78a4cdc6afb8346f8c583862b485`
and `73945eca14ee1866bfa6f96de09bf5744dce485d`, rather than by additional
file-specific normalizations. Their parser-theory unit suite is green; the full
verified compiler build is still running.

Once that exact build yields a compiled runtime, acceptance requires a fresh
complete normalized `Glpk_link` load from a clean predecessor, evaluation of
the pure `convert_to_list pentstring` result, and a regenerated action-zero
cumulative replay. Until those checks pass, this document records a candidate
and the real first failure only.
