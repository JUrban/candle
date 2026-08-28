# Great 100 manual mapping audit

Pinned-source audit performed 2026-08-28. This audit selects theorem value
boundaries only; it does not provide expected identities or turn a load pass
into S1 evidence.

## `100/cantor`: remains manual review

The initial Great-100 source called the proper arbitrary-set cardinality result
at line 25 `CANTOR`:

`!s:A->bool. s <_c {t | t SUBSET s}`.

Commit `f83edb403c09683acf313c030e9a68ef5cb73fcc`, whose stated purpose was to
add Cantor variants, appended a second `CANTOR` at current line 62:

`!f:A->(A->bool). ~(!s. ?x. f x = s)`.

The second binding shadows the historical Great-100 binding. Although the
statements express related forms of Cantor's theorem, structural fingerprints
are different and the original value is no longer addressable after the load.
Pinned source does not say whether historical continuity or the final visible
binding controls acceptance. The mapping therefore remains `manual_review`.

## `100/fourier`: remains manual review

The source independently headlines and proves at least four materially
different candidate results:

- `FOURIER_SERIES_L2` (line 1424): L2 convergence;
- `FOURIER_DINI_TEST` (line 3368): pointwise convergence under Dini's test;
- `FOURIER_JORDAN_BOUNDED_VARIATION` (line 3740): Jordan convergence for
  bounded variation;
- `FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE` (line 4644): Fejer/Cesaro convergence
  for continuous periodic functions.

The file title says “basics of Fourier series,” and the section comments name
each result, but no comment designates one theorem—or the proposed four-theorem
set—as the canonical Great-100 boundary. These statements are not mere proof
rebindings of one identity. The proposed set remains explicit but
`manual_review` pending an external acceptance decision.

## `100/piseries`: audited

Immediately after the general `HARMONIC_SUMS` theorem and its `mk_harmonic`
specializer, the source opens a section labeled “Isolate the most famous
special case” and binds exactly:

`let EULER_HARMONIC_SUM = mk_harmonic 2;;`

This is a direct source designation of the intended named result. There are no
shadowed declarations. The mapping to `EULER_HARMONIC_SUM` is now `audited`.

## `100/quartic`: audited

`QUARTIC_CASES` occurs three times. The first (line 140) proves a one-way
four-case implication. The second (line 163), under “nearly what we wanted,”
strengthens it to an iff characterization. The final binding (line 186), under
“This is the automatic proof,” has byte-for-byte the same quoted theorem
statement as the line-163 binding and replaces only its proof with
`REAL_FIELD`.

Thus the final visible `QUARTIC_CASES` is the unambiguous identity boundary:
the only late shadowing preserves the theorem statement exactly. The mapping
is now `audited`.
