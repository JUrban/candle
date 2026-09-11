# Direct Flyspeck boundary 02: value, structure, and comment batch

Status: DEVELOPMENT / NON-RELEASE. This note makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The exact cumulative `000--049` run at Candle
`2368bca7dab0357d490664dddc1c8f5e2e1cde26` reached 43 actions and passed
42. Actions `000--041` are the exact green prefix (42/42). In particular,
`00-base-through-029` is now 30/30 direct actions green, and the cumulative
arithmetic boundary through action 037 is 38/38 green.

Action 042, `text_formalization/nonlinear/ineq.hl`, cleared the previous
structure parser rollback and reached real CakeML inference. It then failed at
the first mutable binding with:

```text
ERROR: Value restriction violated at line 20

let ineqdoc = ref []
```

Boundary `02-nonlinear_support-through-049` remains open. Full direct S2
remains open; nonlinear and LP/S3 remain open.

The immutable run root is
`/project/flyspeck-candle-runs/v19-dev-direct-boundary02-2368bca-attempt-001`.
Its development result receipt has SHA-256
`6728d5fe32715ddb601aaa49ef67565f02d32d974675079026c6766dc439cf10`;
the Candle log has SHA-256
`d81f5a1243fd2863ead9e5e4361e462d111a37221fd01cc46abd93e16d126158`.
The run took 53:15.15 at 99% of one CPU with maximum RSS 4,331,264 KiB.

## Complete available failure set

After preserving the exact failure, an exact-effective-byte parser sweep of
the remaining boundary sources used the same quotation expander and real
linked Candle parser. It is a focused DEVELOPMENT probe, not cumulative
credit. It found:

- Action 042, `ineq.hl`: the exact run's current value-restriction failure.
- Action 043, `main_estimate_ineq.hl`: the same anonymous module-structure
  family previously exposed in `ineq.hl`.
- Action 046, `parse_ineq.hl`: a distinct lexer failure inside the prior
  normalization's disabled CFSQP region.
- Actions 044, 045, 047, 048, and 049 parsed through to their expected missing
  dependency during isolation; no additional parser class was exposed.

Historical inspection of `fix-top100`, PFT, and relevant Candle branches
found no source correction for these bindings. Flyspeck `upstream/native`
removes the `Ineq` and `Main_estimate_ineq` module wrappers, but that relies on
native file-module behavior and is unsuitable because direct downstream
sources use those namespaces. Historical changes are therefore leads only and
were not copied as authority.

## Coherent compatibility batch

### Ineq value restriction

All uses force `ineqdoc` to one type: a reference to a list of
`texmarker * string * string` triples. The hash-pinned replacement states that
type on the same empty reference:

```ocaml
let ineqdoc = ref ([]:(texmarker * string * string) list);;
```

It changes neither the initial value nor later mutation behavior. A focused
Candle fixture proves that the unannotated binding fails the value restriction
and the annotated binding accepts the same registration. Native OCaml proves
that the original and annotated forms produce the same list. The complete
quote-expanded `ineq.hl` candidate now clears both the former parser rollback
and the new value-restriction error. Its normalized identity is 122,215 bytes,
SHA-256
`d7288af08bf8311f44beff0f13031305054b26a0eecf3f00be8ac81bd2cdc0b5`,
MD5 `fa964b7a0a9808efd3ca2cb008955b93`.

### Main_estimate_ineq structure effects

The contract mechanically enumerates all 92 anonymous structure phrases in
this module: 71 `add`, 12 `addtex`, eight `skip`, and one outer iteration.
Each exact physical line is authenticated before mutation. Wildcard bindings
evaluate the identical expression once at the same initialization position
and discard its result. The first `addtex` ends in a single semicolon in the
original sequence; the normalized form explicitly terminates that wildcard
binding before the next one. Native OCaml proves the same effect order for
both spellings.

The complete exact quote-expanded candidate parses in real Candle through to
its expected isolated missing `Ineq.mk_tplate` dependency. Its normalized
identity is 57,136 bytes, SHA-256
`063af455abdfb9510d33f2eaf36517749df321709c99326f6c71969da1c3d67d`,
MD5 `e8e1e16f6c9c6a6eaaebe5fa7d93dc4e`.

### Parse_ineq disabled CFSQP span

The earlier two-operation normalization surrounded the unauthorised CFSQP
generator with `(* ... *)`. The disabled C++ format text itself contains
`void*)`; Candle's comment lexer treated that byte sequence as the comment
terminator and later failed on a string escape. This was a normalization
defect, not a Flyspeck source or semantic failure.

One exact span replacement now authenticates original lines 408--449 by
SHA-256 and replaces the complete generator with the same fail-closed
`cc_code` stub. There is no comment-delimiter interpretation and no process
authorization. The complete quote-expanded candidate parses in real Candle
through to its expected isolated missing `Sphere` dependency. Its normalized
identity is 21,863 bytes, SHA-256
`cc5958c1de5c3b115336455d60e9b6a295625ef2d66e03c6f1ef2c2c6b619090`,
MD5 `3b10c8f609bfd428258df064ed785c90`.

No inequality, theorem statement, hypothesis, proof step, proof intent, tag,
or allowed axiom changes in this batch. CFSQP execution remains fail closed.

## Validation before cumulative execution

- focused native-OCaml/Candle compatibility oracles: pass;
- normalizer, manifest, and all-inventory tests: 63/63 pass;
- frozen-byte manifest fixed-point check: 297 roots, 400 source nodes, and 43
  generated inputs pass;
- parser descriptor checks: 20/20 pilot and 400/400 inventory pass;
- source profile: 355 exact original plus 45 exact normalized inputs;
- quotation expansion: unchanged at 318,813 quotations;
- generated programs: MD5 `e2f1e890585053d6c191992f04e5333c` and
  `36523671a97075e4a06d2f7775f1c2b0`;
- manifest: SHA-256
  `914f221d6e7e8bbe76f878bd64b4a7eb1f6152159e442987552b874310532156`;
- normalization contract: SHA-256
  `97c90baa261a3cbc2f17657b2bbcccbf7bbe564f51cf260cc352ede0ee5147e4`;
- parser descriptors: SHA-256
  `3b98bf5de3a1b47e9c1ab32b4a0ff6d707c82105c0788af9b6d784c6e593addf`
  and
  `74dc2fdd84bb63a35eec601d7be1d845a09220b7aa13d234c09045e541129ce0`;
- ordered effective/prepared 400-source roots:
  `061440028e09a366f956ea16af0d83075edd385e500bbc73a408e49045844448`
  and
  `0f7eb8ea79faacb93066a03526647879b5f21c5fb222ec906000873fd73e0aef`;
- JSON parsing and `git diff --check`: pass.

The broader stratum-runtime unit file's one pre-existing host-Python pin error
remains unchanged from the clean parent and is not expanded into assurance
work in this functional loop.

## Next direct step

Commit the exact combined bytes, materialize a fresh normalized overlay and
stratum plan, and rerun cumulative actions `000--049`. Only that exact run may
credit action 042, action 043, or action 046 and may close boundary 02.

Headline status: 43 reached / 42 passed; exact cumulative prefix 42/42;
boundary 00 is 30/30 green; boundary 02 open; three observed compatibility
classes corrected in the next batch but awaiting exact cumulative validation;
full direct S2 open; nonlinear and LP/S3 open.
