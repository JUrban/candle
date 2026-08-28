# Exact LP result coverage gate

The pinned Flyspeck assembly in
`text_formalization/tame/linear_programming_results.hl` originally inserted
verified `(id,theorem)` pairs into a hash table with `Hashtbl.add`.  Later
construction looked up every archive id, so a missing id failed, but duplicate
result ids and results outside the archive were not rejected explicitly.

`PROJECT-S3-LP-EXACT-RESULT-COVERAGE-001` is an exact, hash-bound
normalization of the four-line table-construction block.  Before final theorem
construction it now:

1. builds the expected-id table while rejecting a duplicate archive id;
2. rejects every verified-result id not in the expected table;
3. rejects every duplicate verified-result id; and
4. requires the verified-result count to equal the archive-id count.

Unique expected ids, unique result ids, the subset check, and equal cardinality
together establish equality of the two finite id sets.  The existing ordered
lookup and theorem conversion then consume every expected id.  The original
`let result = []` shadow is retained so the nested verification-result wrapper
can be reclaimed before the long final construction.

This is a fail-closed bookkeeping strengthening, not LP evidence.  It neither
creates a theorem nor weakens `verify_lp_certificate`; S3 still requires the
authenticated compiled direct run to verify all 39 certificate files, reach
the final theorem, match the approved theorem/hypothesis/axiom fingerprints,
and reproduce those observations in a second clean run.  A PFT replay cannot
satisfy this gate.
