# Direct Flyspeck 00--029 failure-set diagnostic at 8afc454

The current exact cumulative result remains **3 actions reached / 2 passed**
at `00-base-through-029`.  A separate DEVELOPMENT / NON-RELEASE diagnostic
invoked all 30 actions on the same ordered boundary: 21 completed independently
or were already authenticated, one exposed a genuine failure, and eight failed
only because that dependency had not completed.  This diagnostic is not exact
cumulative evidence and makes no S1, S2, S3, promotion, or release claim.

Full direct S2 remains open.  Nonlinear and LP/S3 remain open.

## Complete available failure set

Actions 000--013 completed without a diagnostic, including actions 005 and 006
after the preceding REBIND compatibility batch.  Action 014 then reported:

```text
014 leg/collect_geom.hl:
ERROR: Type mismatch between thm and (thm list -> term -> thm) -> _10 at line 430
```

The diagnostic pointed at `MAX_REAL3_LESS_EX`, but that theorem and its immediate
dependencies are not defective.  Actions 016--020 and 028--029 also completed.
The eight remaining failures are dependency cascades:

- action 015 requires completed `collect_geom.hl`;
- action 021 and action 024 require members of `Collect_geom`;
- action 022 requires action 021's completed `real_ext.hl`;
- action 023 and action 027 require completed `Tactics_jordan`;
- action 025 requires the action-024 dependency before its dynamic load; and
- action 026 requires completed `Float` after action 025.

Every `AFTER` marker was treated only as REPL continuation.  It did not override
an error or establish action success.

## Historical inspection and localization

Before editing, Candle branches `origin/fix-top100`, `origin/pft`,
`origin/ptr-eq`, and `origin/merge/jrh13-master-20260825` were searched for the
source and construct.  They contain no applicable patch.  The pinned Flyspeck
origin/master, upstream master/develop/native, and historical Candle-replay
branches retain the same theorem and following expression.  They supplied no
correction to adopt.

Small faithful modules containing `max_real`, `max_real3`,
`MAX_REAL_LESS_EX`, and the original `MAX_REAL3_LESS_EX` passed under Candle.
A larger helper module containing the nearby `SET_TAC`, `PHA`, `DAO`, and
`NHANH` definitions also passed.

A single persistent Candle process then loaded the exact direct setup and
actions 000--013.  The original full normalized `collect_geom.hl` reproduced
the action-014 diagnostic.  Explicit theorem, quotation, list, and tactic type
annotations did not change it.  Moving and splitting definitions caused the
reported theorem to move, while a module ending immediately after
`MAX_REAL3_LESS_EX` passed.  This localized the real construct to the following
anonymous theorem-valued module expression at original line 720:

```ocaml
MESON[]` (!x y z. ...`;;
```

Changing only its module binding form to:

```ocaml
let _ = MESON[]` (!x y z. ...`;;
```

made the complete 103-KiB source load successfully through its last export,
`Collect_geom.UPS_X_SYM`.  The earlier theorem diagnostic was therefore another
instance of the established CakeML anonymous module-expression class, not a
type defect in `MAX_REAL3_LESS_EX` and not a mathematical failure.

## Bounded correction and focused validation

The normalization contract adds one hash-pinned exact replacement at line 720.
The wildcard binding evaluates the identical `MESON` expression once at the
same module-initialization position and discards the same theorem result.
Evaluation order, effects, exceptions, theorem construction, every theorem
statement, hypothesis, and proof body remain unchanged.  The resulting exact
normalized source identity is 103055 bytes, MD5
`dc8885bd34830d81ed0ff10e0f26aad8`, and SHA-256
`deeedd4c0cbd1e2dc9250c1513b37ea2566ddd0b10dcee4974c27f0ee2daf378`.

Focused validation passed:

- an original theorem-valued anonymous-expression fixture reproduced the same
  `thm` versus `MESON`-function diagnostic;
- the wildcard form loaded and preserved both surrounding module exports;
- the full persistent-source candidate loaded through `UPS_X_SYM`;
- the native OCaml effect/order oracle remained green; and
- the combined focused gate passed with exactly its six intended negative
  diagnostics and no unexpected error.

The frozen focused-probe directory is
`/project/flyspeck-candle-runs/v16-persistent-collect-geom-8afc454-probe-001`.
Its persistent Candle log SHA-256 is
`7cca4a9920d8444461a43a222928b0d31539ebd1c6bee8c82e977f97a7e17667`,
its focused gate log SHA-256 is
`83994ff79fa7a809df5a513e2678710a59158cb5aacfd2f0a159c92e06e816a8`,
and its development receipt SHA-256 is
`dd2d5e1e5c7eec425b45eb3717d8fbd5bcdc06e2e1da758311394fb4fa898278`.

## Preserved all-action diagnostic

The frozen run is
`/project/flyspeck-candle-runs/v16-dirty-all-actions-00-029-8afc454-run-005`.
Its log SHA-256 is
`bb3bda6baa83c93ff60edf23e31fe14b26e384a6ec2467cce327f33b3f8e907f`,
its timing SHA-256 is
`0bd02f7047709c1374bb08a959cb7638004d6d81f6a37b516a13bcc70deb7630`,
and its result-receipt SHA-256 is
`7eef52e300323c28bdc7ad7aa60233cb287de9636f919d0b49c54c3752250a91`.
It used 43:18.72 wall time, one CPU, and 4,339,328 KiB maximum RSS.

The next gate is a fresh complete 00--029 development replay on committed
bytes.  Only its exact cumulative action markers may advance the official 3/2
progress metric.
