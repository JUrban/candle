# Direct Flyspeck boundary 04: complete v34 dirty failure set

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE diagnostic only. This report awards no
exact cumulative action, S1, S2, S3, qualification, promotion, or release
credit. No qualified Great100 byte was changed.

## Headline direct status

The latest completed exact cumulative replay reached action 079 and passed all
79 actions 000--078. Its failure receipt has SHA-256
`e0b1507d883e6c088143d6d8d31220bfe407ccd65ee668d5fae40336ad0e52e1`.
Thus the exact headline remains **80 reached / 79 passed** while the v34 exact
replay runs independently from action zero.

The v34 dirty collector then attempted actions 000--151 as distinct REPL
phrases and emitted all 152 begin markers, all 152 after markers, and one final
diagnostic-complete marker. It exited zero by design after 1:16:15, with a
maximum RSS of 4,481,792 KiB. The 25,516,011-byte transcript has SHA-256
`4bb0c4c1d2283d7e5956fb08fbeff5169ad957a3bfdebc3cfaf9952b46e5931f`.
The immutable result receipt is
`/project/flyspeck-candle-runs/v34-dirty-failure-set-boundary04-8b8095c-attempt-001/development-diagnostic-result.json`,
SHA-256
`0e16cb29c73e9720204dd290fc86c53d63b2043213a4060ef8b0079349051c3e`.

## Failure inventory

Fifty-two actions emitted a failure diagnostic: 32 `ERROR` diagnostics, 17
runtime/load exceptions, and three parser-recovery failures. Four sites are
independent-looking root candidates; only the first has yet been reached in a
clean cumulative replay:

1. action 079, `local/WRGCVDR.hl`: theorem-valued module structure effect;
2. action 089, `packing/AJRIPQN.hl`: `linear_ineqs: no contradiction` during
   the main refinement proof;
3. action 102, `packing/YSSKQOY.hl`: `prove_by_refinement: has stv`; and
4. action 126, `../jHOLLight/caml/ssreflect.hl`: unary term-list `setify`
   under Candle's comparator-explicit API.

The complete set of other diagnostic actions is:

```text
080 081 082
090 091 092 093 094 095 096 097 098 099
101 103 104 105 106 108 109 110 111 112 113 114
117 118 119 120 121 122 123
128 129 130 131 136
141 142 143 144 145 146 147 148 149 150 151
```

These are currently classified as secondary or error-recovery observations,
not compatibility roots. They consist of undefined modules or theorem names,
strictbuild dependency reload failures, cache-skip identity failures after a
partial load, and `Expected to be at EOF` parser recovery after earlier source
errors. A clean cumulative replay must promote or dismiss them.

## Validated implications

- The v33 action-072 `SLTSTLO` term-`setify` repair is independently exact
  green; actions 073--078 also pass.
- The v34 action-083 `Inequalities` goal-effect repair passed in the dirty
  collector, although dirty execution awards no exact credit.
- The v34 action-126 instantiation-propagation code typechecks through both
  combinators. Loading then reaches the distinct `get_context_vars` unary
  term-`setify` site.
- Historical Candle `fix-top100` refs have no copies of the three Flyspeck
  sources, and the relevant current Flyspeck refs share identical source
  blobs. Historical changes are leads only.
- Focused independent probes reproduce and eliminate the action-079
  theorem-valued structure effect and action-126 comparator-explicit term-list
  failure without changing theorem statements or proof content.

## Next cumulative experiment

The coherent next source state combines the action-079 wildcard-binding repair
and action-126 canonical term comparator. It must be replayed from action zero.
The first clean result at or after action 089 will determine whether `AJRIPQN`
is the next genuine blocker; action 102 and all recovery-state observations
remain provisional until reached with every predecessor green.
