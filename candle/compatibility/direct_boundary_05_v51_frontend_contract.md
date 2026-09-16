# Direct boundary 05: compiled frontend compatibility contract

Status: DEVELOPMENT / NON-RELEASE. The verified compiler build and focused
compiled gates are complete. They authorize a fresh cumulative functional run;
they do not themselves add a Flyspeck action marker or make an S1, S2, S3, or
release claim. The accepted cumulative metric remains 152/152 actions, indices
000--151.

## Verified build identity

The exact CakeML source commit is
`73945eca14ee1866bfa6f96de09bf5744dce485d`, following the `for`-loop lowering
commit `8dc5e5d9618d78a4cdc6afb8346f8c583862b485`. The complete serial build ran:

```text
/project/worktrees/HOL-cakeml-dopen-v13/bin/Holmake -j1 --mt=1 cake.S
```

All 20 stages completed, including the final `x64Bootstrap` theorem and output,
in 9h24m48s with exit status 0. Maximum RSS was 75,189,308 KiB and no swaps were
reported. The preserved development build directory is:

```text
/project/flyspeck-candle-runs/nonpromotable-caml-frontend-full-build-73945eca1-attempt-001
```

Its `build.log` has SHA-256
`040bec14a328c82fe379c1a30b7263988629059c220447b341279b31d58ccaa8`,
and `time.txt` has SHA-256
`3e12d144ad2a890a52afdcf04390374b6d3cb00193995de3256d1aca6f71f0f7`.
The generated assembly has SHA-256
`f7f15a86bf11a1c1b2b5e1e05191a28992fd4b60cd7174a1c3f35c23d1035c3b`,
and its configuration has SHA-256
`a0ba4d7b3f9dde5ba88d89b4eaba6be750f816b2389937394813eb44bd5ced4d`.

The first exact development link used Candle commit
`51909d006d0b92604503b51d5ae5c65f2b36af34` and produced the 1,189,767,392-byte
runtime with SHA-256
`3aaa248c0d5d6c96fa8e36445d1a945a751f0cf11a8b734a6142e9fab1088b2b`.
It is explicitly nonpromotable; a final exact link is required after the Candle
contract and reports are committed.

## Accepted compiled behavior

The native-OCaml/compiled-Candle gates pass for:

- ascending, descending, and empty `for` loops, including single evaluation of
  bounds, lexical loop-variable behavior, independence from shadowed arithmetic
  and comparison operators, endpoint handling without an overflow step, and
  exception propagation;
- the one- and two-level indexed assignments used by the authenticated Flyspeck
  graph, including alias-visible mutation, unit result, and bounds exceptions;
- the exact action-153 fail-closed formatter binding and its distinct integer,
  string, float, and mixed-arity instantiations.

These passes retire the transient loop and indexed-assignment source rewrites
used during the action-152 focused probe. The exact Flyspeck sources can use
their native constructs in the fresh cumulative replay.

## Deliberately unaccepted behavior

The standalone-module-expression part of the frontend batch is not accepted.
After correcting unrelated fixture assumptions (Candle's value restriction,
the absence of `max_int` in the boot slice, and unavailable array literals), a
minimized structure containing a prior binding followed by a bare effect
expression still reported that prior binding as undefined. A separate
anonymous `7;; true;;` sequence also failed to preserve the expected structure
typing/scope. The original multi-cause diagnostic run is preserved at:

```text
/project/flyspeck-candle-runs/v106-frontend-loop-gate-scaffolding-failure-73945eca1-51909d0-dev-001
```

The isolated open defect is retained as
`compatibility/fixtures/ocaml_structure_effect_scope_deferred.ml`; native OCaml
binds its final result to `true`, while the current compiled frontend reports
`effects` undefined at the bare assignment.

Accordingly, no general claim is made for anonymous standalone module
expressions. Action 153 instead uses one hash-pinned, OCaml-equivalent
`let _ =` wrapper around a pure example. This is the cheapest faithful current
frontier repair and avoids another nine-hour compiler build while the direct
functional lane remains open.

## Next acceptance boundary

The generated manifest and its normalization/source-digest programs must reach
a fixed point, after which the exact committed Candle head must be relinked.
A fresh 000--184 cumulative run then decides the source-level contract. It must
authenticate action 152, load the complete normalized action-153 source and its
pure result, and collect the complete available failure set through the LP
support boundary. Focused gates do not substitute for those action markers.
