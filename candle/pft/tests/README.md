# PFT consumer tests

`fixtures/core.pft.bin` and `fixtures/unauthorized-axiom.pft.bin` are generated
by HOL4's `generate-candle-fixture.sml` on the pinned replay branch.  They are
committed here so the Candle endpoint has a stable cross-repository golden
input; regenerate them rather than editing the binaries by hand.

Run `./candle/pft/tests/run.sh` from the Candle repository root.  The harness
first replays the golden trace, then creates deterministic corruptions and
checks that each one is rejected in a fresh Candle process.  A structurally
valid AXIOM trace is also required to fail under the default-deny policy.
