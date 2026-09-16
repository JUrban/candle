# Direct boundary 05: action 153 GLPK-link compatibility

Status: DEVELOPMENT / NON-RELEASE candidate. The first genuine action-153
failure is reproduced, the narrow normalization gates pass on the rebuilt
frontend, and the verified compiler build is complete. The complete normalized
source has not yet passed a fresh cumulative action-zero replay. The cumulative
metric therefore remains 152/152 actions, indices 000--151; neither action 152
nor action 153 receives cumulative credit from this work.

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
historical changes do not supply a compatibility solution. The candidate
begins with one exact hash-pinned replacement of the alias:

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
rebuilt frontend correctly accepts this source's native ascending `for` loop,
but its anonymous standalone module-expression lowering does not retain prior
module bindings. The one affected pure example is therefore made explicit in
the exact source contract:

```ocaml
let _ = wheremod [[0;1;2];[3;4;5];[7;8;9]] [8;9;7];;  (* 2 *)
```

This is OCaml's equivalent discarded-result binding: it evaluates the same
pure call and discards the same result. It is not a general anonymous-expression
workaround or evidence that the central lowering works. The two-operation
normalized file is 8,085 bytes, SHA-256
`c09fc08aba4b758b7b46250d783414b88828c53b40fefb187f92b675d0ba96b9`,
and MD5 `eac0c846a4608adb32137e0a61029f55`.

The fail-closed oracle exercises integer, string, float, and mixed-arity call
shapes under native OCaml and the rebuilt compiled Candle. It confirms the
polymorphic binding and the exact deterministic failure at every call. The
normalization gate also checks the exact explicit discarded-result expression.
The normalization contract and complete manifest have reached a fixed point at
80 entries (79 selected overlays), contract SHA-256
`cf4ac5348a3f6550824cf218c20a4f92f46aa75ab7d868ccd168d893b8b41e57`,
297 roots, 400 source nodes, and 43 generated inputs.

## Remaining acceptance

The exact CakeML commit
`73945eca14ee1866bfa6f96de09bf5744dce485d` completed a serial verified build
through `x64Bootstrap`. Its compiled native/Candle gates pass for native `for`
loops, one- and two-level indexed assignments, and this fail-closed formatter
contract. Anonymous standalone module expressions remain a separate central
frontend defect, which is why the exact pure example wrapper above remains in
the source contract.

Acceptance still requires a fresh complete normalized `Glpk_link` load in the
regenerated cumulative plan, evaluation of the pure `convert_to_list pentstring`
result, and its authenticated action marker. Until that action-zero replay
passes, this document records a candidate and the real first failure only.
