# Selected Flyspeck Unix telemetry contract

## Decision

The direct Flyspeck route does not expose an ambient wall clock.  Its
`Unix.gettimeofday ()` binding returns `Float.zero`, and the authenticated
external runner owns wall time and RSS measurements.

This is an explicit selected-route substitution, not an implementation of
OCaml's `Unix.gettimeofday` semantics.  It avoids adding a nondeterministic
clock FFI to the proof process while allowing proof-producing computations
wrapped by legacy timers to execute.

## Exact source boundary

The pinned 400-node manifest contains exactly four qualified uses:

- `formal_ineqs/misc/misc_functions.hl:43,48`, bracketing repeated application
  of a function.  The first tuple projection is the function result; only the
  second projection is elapsed telemetry.
- `formal_lp/hypermap/verify_all.hl:65,67`, bracketing certificate
  verification.  Each returned theorem/result list is paired with elapsed
  telemetry.  `linear_programming_results.hl` flattens the first projections
  to construct the result table; it sums the second projections only for the
  `Total verification time` report.

The manifest generator records those four coordinates under
`static_library_contract.binding_evidence["unix.cma"].telemetry_uses` and its
unit test rejects additions, removals, or movement.  A new selected clock use
therefore reopens this audit before it can enter a release manifest.

For each current use, replacing both timestamps by the same value preserves
the wrapped computation, its effects, exceptions, and returned proof object.
It changes only the elapsed subtraction to zero.  The release semantic
fingerprints exclude timing text but include theorem/definition/assumption
content; structured external timing remains required by the project release
gate.

## Regression and remaining Unix boundary

`test_unix_metadata.sh` verifies with compiled Candle that:

- `date` and `whoami` remain manifest-file substitutions;
- two clock reads and their elapsed subtraction are deterministic zero;
- a representative timed computation still returns its original result;
- arbitrary process commands, bidirectional process creation, directory
  creation, and `Sys.command` remain fail-closed.

`Unix.mkdir`, `Unix.open_process`, and `Unix.close_process` are not enabled by
this contract.  The separately normalized LP input path removes the selected
runtime need for archive extraction; GLPK generation/debug process helpers
remain definitions whose execution must fail until a sandbox/refinement
contract exists or the complete selected run proves non-use.
