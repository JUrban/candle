# Direct Flyspeck boundary 02: dirty nonlinear failure-set probe

Status: DEVELOPMENT / NON-RELEASE. This note makes no S1, S2, S3,
qualification, promotion, or release claim.

## Actual direct progress

The persistent dirty `000--049` diagnostic at Candle
`6e29dae6b72d2a203ef0ccf26e1e81ac784d7e21` reached all 50 requested
actions. It recorded 44 successful or already-authenticated loads and six
failed/cascaded actions. In particular, action 038
`text_formalization/nonlinear/calc_derivative.hl` passed directly, so the
exact cumulative green prefix is now 39/39 actions (000--038). Boundary 02
remains open pending an exact cumulative rerun.

The immutable diagnostic is
`/project/flyspeck-candle-runs/v17-dirty-all-actions-00-049-6e29dae-run-001`.
Its log SHA-256 is
`0f7c86ac7d897906f6abbb217c3403eeeaa5b35509cbfc5fa5fcd8217812aa09`;
its development receipt SHA-256 is
`a5580a9eabcb0fdc538ff8f2196e1502ab5585c838e7a91576f1bd050e9d5830`;
and its timing record SHA-256 is
`5cd445ca5de4456058b83c65bd9d55abc75ccf033233f64078e2e8711f65d410`.
The interpreter reached clean REPL EOF in 48:55.44 with a 4,339,328 KiB
maximum RSS.

## Complete available failure set

- Action 039, `ineqdata3q1h.hl`: CakeML inferred a local `List.nth` alias at
  one element type and rejected its later use at another element type.
- Action 042, `ineq.hl`: refused the already-failed action-039 dependency;
  this is a cascade in the dirty session.
- Action 043, `main_estimate_ineq.hl`: failed at the module opener after the
  preceding failed dependency; this is dirty parser-state fallout, not a new
  parser-inventory failure. The same source is in the established 400/400
  parser inventory.
- Action 046, `parse_ineq.hl`: CakeML's integer-only `<` was applied by
  `sort (<)` to a string list.
- Action 047, `optimize.hl`: `Ineq.add` was undefined because action 042 had
  not loaded; this is a cascade.
- Action 049, `merge_ineq.hl`: refused the already-failed action-039
  dependency; this is a cascade.

The frozen development receipt classified action 046 as a `nub` alias issue.
That diagnosis is corrected here without modifying the immutable receipt:
the exact minimized reproducer proves that `sort (<)` on strings is the
failing construct, while the typed comparator
`fun left right -> String.compare left right < 0` passes. No arbitrary alias
or basename exception is involved.

## Coherent compatibility batch

Static review of the selected action-039--049 sources, followed by minimized
Cake/native oracles, identifies two live root causes and several masked
CakeML language-library incompatibilities. The bounded hash-locked batch:

- removes only the local polymorphic `nth` alias and uses global `List.nth`
  at its four original call sites;
- gives the string sort its exact typed `String.compare` comparator;
- replaces unavailable `List.flatten` with equivalent `List.concat`;
- expands constant integer `Printf` formats into byte-equivalent string
  concatenation;
- replaces finite `for` loops with `do_list` over the same ascending ranges;
- narrows a unit-only counter reset binding to `()`;
- preserves exact generated strings with direct concatenation; and
- fails closed in the selected direct route for the unused CFSQP C-code
  generator, whose external execution was already disabled by runtime policy.

Native OCaml byte-equality oracles cover all rewritten simple format strings,
including negative and extreme integers and special strings, plus the exact
16-case F4 and 35-case hex loop orders. Focused Candle fixtures reject the two
original inference constructs and accept the normalized forms. The original
Flyspeck checkout and all theorem statements, hypotheses, proof operations,
and allowed axioms remain unchanged.

## Pre-runtime validation

- normalization contract: 45/45 entries and 182/182 uniquely named exact
  operations validate;
- focused Cake/native nonlinear compatibility oracles: pass;
- manifest contract tests: 28/28 pass;
- all-inventory prepared-source tests: 17/17 pass, covering 400 inputs as 355
  exact originals plus 45 exact normalized sources and the unchanged 725
  loader actions;
- parser descriptor regeneration/check: 20/20 pilot and 400/400 inventory;
- manifest regeneration: 297 roots, 400 source nodes, 43 generated inputs;
- JSON validation and `git diff --check`: pass.

The broader parser-controller unit file has a pre-existing quotation-contract
anchor mismatch: its quotation model pins CakeML `8a892690...`, while the
already-established direct manifest pins the linked integration at
`cea7c49d...`. The same focused failure reproduces unchanged at parent
`6e29dae`. It is not caused by these six normalizations and is not expanded
inside this functional compatibility loop.

## Next direct step

Regenerate and validate the 400-source manifest, overlay, and direct plan for
the exact batch bytes. Then rerun actions 000--049 cumulatively. Only that
exact direct run can credit boundary 02 as 50/50 or expose the first genuine
remaining Candle/Flyspeck failure.

Headline status: dirty diagnostic 50 reached / 44 passed; exact cumulative
prefix 39/39; boundary 02 open; full direct S2 open; nonlinear and LP/S3 open.
