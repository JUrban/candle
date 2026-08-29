# Canonical CakeML bootstrap transition

The canonical bootstrap receipt remains valid only at the exact Candle root and
commit which launched it.  `cakeml_bootstrap_transition.py` does not edit,
translate, or relax that receipt.  It validates the receipt with the unchanged
schema-5 validator at its recorded source checkout, then proves that a named
later Candle checkout has the same Candle-side bootstrap/link inputs byte for
byte.

The compared closure is:

- `candle/flyspeck_manifest.json` (including the exact CakeML/HOL4 pins),
- `candle/cakeml_artifact_provenance.py`,
- `build-local-cakeml-bootstrap.sh`,
- `candle/cake.S.patch`, and
- `candle/insulate.py`.

The first three are the Candle-side causal bootstrap inputs.  The patch and
generator are included because they transform the authenticated bootstrap
outputs during the local link.  `build-local-cakeml.sh` and the transition
controller are not bootstrap inputs: they are the new destination-side
consumer.  Their exact bytes are authenticated by the required clean final Git
commit and by the final linked-provenance record.

Both Candle checkouts and the CakeML checkout must be exact clean Git top-level
directories at caller-supplied 40-hex commits.  Grafts, replacement objects,
assume-unchanged flags, skip-worktree flags, non-ignored untracked files,
non-stage-0 input entries, source/final root reuse, non-descendant final
history, and any closure difference are rejected.  Ignored build products are
permitted, but every closure member is separately matched to its committed
blob.  The bootstrap and transition receipts must be ordinary files outside all
authenticated worktrees.

The transition JSON is proof data, not a signature and not an authority.  Its
checker reconstructs the complete record from the explicit roots and heads and
the live original receipt.  Editing all claimed hashes therefore does not make
a forged record acceptable.  Transition linking materializes an ordinary
`candle/build/bootstrap-transition.json` copy and emits the distinct schema-7
`candle-linked-pinned-cakeml-transition` linked record.  That record binds the
copy, the transition/link controller source closure, the retained canonical
bootstrap evidence, and both committed closure sides.  Direct diagnostic
runtime snapshots archive the transition copy through the linked-output
inventory.

Schema 7 is explicitly diagnostic-only.  It is never interchangeable with the
ordinary exact-root schema-6 record: the Great 100 promotion gate continues to
require schema 6.  A final S1/S2 release therefore still requires a new
canonical bootstrap at the final Candle head and the original two-argument
exact-root link.  Removing the schema-7 discriminator or transition copy makes
the diagnostic artifact fail closed rather than resemble schema 6.

After the canonical receipt exists, create the transition record outside every
worktree:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S \
  FINAL_CANDLE/candle/cakeml_bootstrap_transition.py \
  record-transition \
  --source-candle-root SOURCE_CANDLE \
  --source-candle-head SOURCE_HEAD \
  --final-candle-root FINAL_CANDLE \
  --final-candle-head FINAL_HEAD \
  --cakeml-root CAKEML \
  --bootstrap-record BOOTSTRAP_RECEIPT \
  --write TRANSITION_RECEIPT
```

Then use the explicit transition form of the existing build command:

```sh
FINAL_CANDLE/build-local-cakeml.sh \
  CAKEML BOOTSTRAP_RECEIPT SOURCE_CANDLE SOURCE_HEAD TRANSITION_RECEIPT
```

The original two-argument command remains the promotable exact-root schema-6
path.  Transition mode checks the proof before copying bootstrap outputs,
checks it again in the schema-7 linked-record controller, and uses the schema
6/7 dispatcher for later diagnostic launches.  If the bootstrap receipt is
absent, neither command is authorized and no transition/link should be
attempted.

Trust assumptions retained from the canonical receipt include kernel,
filesystem, process, exact host-tool semantics, and absence of hostile
same-UID transient mutation between guarded observations.  The transition adds
no claim that the retained CakeML/HOL4 artifacts were independently rebuilt;
their original trust-boundary statement remains controlling.
