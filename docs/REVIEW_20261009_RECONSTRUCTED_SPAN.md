# Terminal reconstructed Q-span, 2026-10-09

## Checked endpoint

`Quillen/Waldhausen/QuillenComparison/ReconstructedSpan.lean` is checked
and frozen. The endpoint `reconstructedRow_last_step` identifies the
**actual last adjacent Q-arrow** of the actual recursively reconstructed
exact row. After its specified target identification, this arrow equals

```
reconstructedInitialChainIso.hom.app (Fin.last n)
  ≫ qIsoOfIso(centralTopIso F).hom
  ≫ Q.mkHom { apex := P, l := p, r := r, wl := hp, wr := hr }.
```

The assumptions are an arbitrary exact category, its original actual exact
row `F`, the actual deflation `p` onto that row's initial-flag top, and the
actual inflation `r`. No caller-supplied pullback existence, span equality,
chain realization, or essential-surjectivity hypothesis is needed.

## Identification details

* The two initial index lemmas, handed over by the Q/S author, are checked
  here: the penultimate interval becomes the whole old middle interval,
  and the final interval becomes the whole extended row.
* `reconstructedTopIso` is the explicit ordinal-index equality followed by
  the actual `extendedRowTopIso`; `reconstructedPenultimateIso` is the
  explicit source index equality.
* `reconstructedRow_last_step_to_whole` applies the actual interval-span
  transport theorem and retains both index casts.
* `reconstructedCentralIsoAt_last_top` proves that the canonical old-chain
  terminal component followed by `centralTopIso F` equals the literal
  middle-row and cokernel-completion identifications. This is naturality
  under the exact old terminal-interval equality, not a replacement by an
  unspecified isomorphism.
* The endpoint combines that equality with the other worker's checked
  `extendedRow_wholeSpan` and `extendedRepresentative_initialFlag`, whose
  conclusion uses precisely the original span legs `p` and `r`.

This supplies the final-span compatibility needed by the separate
essential-surjectivity induction. This report does not claim that induction
or the complete topological Q/S comparison is already accepted.

## Verification

Direct source checking with `lean -j1` under
`/tmp/quillen-lean-slot-1.lock` succeeded and produced an importable olean.
The only source message is a non-fatal unused-section-variable linter warning.
`audits/ReconstructedSpanAudit.lean` checks an arbitrary-universe consumer
and recursively audits every declaration originating in this module,
including private/generated declarations. All **21 declarations passed**
with only `propext`, `Classical.choice`, and `Quot.sound`. The source hash
still matched after the audit.

Evidence:

* `logs/q-s-reconstructed-span.log`
* `logs/q-s-reconstructed-span-axioms.log`
* `logs/q-s-reconstructed-span-hashcheck.log`

SHA256:

```
a01195d607b14fa6b595050f0b93a5eb0cbf46e773a05155d22a6fece20fceab  Quillen/Waldhausen/QuillenComparison/ReconstructedSpan.lean
a719f3c55bb0434e48a6861267906fd26032c35361f16c0388f8dbf524798507  logs/q-s-reconstructed-span-sources.sha256
be1c9e0b9a59fd7dd8547d14ee7a9ad892ed88143f6aa367d5631d166ce41e1e  audits/ReconstructedSpanAudit.lean
07f7c286d8cdc543b1a2b6fb90ba52c4bf9ee30dc44286fcba00d66fdc55ace8  logs/q-s-reconstructed-span-axioms.log
```
