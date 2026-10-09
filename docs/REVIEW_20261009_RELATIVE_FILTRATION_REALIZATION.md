# Independent review: original relative-filtration realization

Accepted 2026-10-09 11:53:45 UTC.

## Frozen scope

- `Quillen/Waldhausen/Fibration/RelativeRows/FiltrationNerves.lean`
- `Quillen/Waldhausen/Fibration/RelativeRows/FiltrationRealization.lean`

Source manifest: `logs/relative-filtration-realization-sources.sha256`.
Both sources were read completely. Neither source nor any live build
artifact was modified during this review.

## Semantic assessment

The categorical forward functor is the actual fine-weak relative-inner-S
interchange followed by the accepted original initial-filtration functor.
Its categorical equivalence composes those two previously proved actual
equivalences. The component is precisely the original initial interval
`[0,i+1]`; no reconstruction is substituted for that forward map.

Both row restrictions commute strictly with this original functor. The
relative direction restricts the same original initial chain; the inner
S direction applies the actual quotient-row reindexing. The fine-weak
nerve maps are therefore genuinely natural before realization.

The first realization equivalence uses the actual original-grid nerve
isomorphism followed by the proved bisimplicial realization theorem on
these categorical equivalences. The second application totalizes in the
relative degree. The final diagonal presentation is identity on the same
three original indices, with its naturality checked. The final homotopy
equivalence has the prescribed original total grid-to-filtration map as
its forward map. Neither application assumes naturality of chosen inverses.

The sole additional structural hypothesis is the base coarse
`ExtensionAxiom`, transported to genuine coarse rows by the accepted row
extension theorem. No cylinder, saturation, or desired realization/fiber
conclusion is an input. The categorical/diagram layer allows independent
object and hom universes. The existing raw S-map realization layer retains
its explicit common-universe scope. The bounded-complex consumer uses the
actual proved complex extension axiom without kernel/cone/shift closure
assumptions.

This proves the original relative total S-realization comparison with the
mixed cofibration model. It does not by itself assert the global
homotopy-fiber or Gillet-Waldhausen theorem.

## Independent validation

A separate first-path Lean overlay excluded every target artifact family,
then rebuilt both target sources from their frozen bytes. All target
imports resolve to fresh regular files, verified by `lean --deps`.
The focused source checks and independent audit are warning/error-free.

`audits/RelativeFiltrationRealizationIndependentAudit.lean` performs one
environment traversal and recursively checks every declaration from both
origins against only `propext`, `Classical.choice`, and `Quot.sound`.
The fixed count is **44 = 16 + 28**.

All **25 consumers** pass. The author's 18 are retained; seven additions
check the original mapped natural-transformation component, exact inverse
categorical composition, inverse full-diagonal identity, actual grid/nerve
composite, the original total grid component, equality with the original
degreewise simplex map, and the genuine zero simplex in degree zero.

Before/after checks cover both target sources, **3,734 prerequisite
sources**, **17,231 dependency artifacts**, and the toolchain/project pins.
Every hash is unchanged. The prior standalone authored boundaries are
used as frozen prerequisites; no unverified equivalence is assumed.

## Evidence and replay

- Directory: `logs/relative-filtration-realization-independent-20261009/`
- Replay: `logs/verify-relative-filtration-realization-independent.sh`
- Preparation: `logs/prepare-relative-filtration-realization-independent.py`
- Driver: `logs/relative-filtration-realization-independent-driver.log`
- Audit: `audits/RelativeFiltrationRealizationIndependentAudit.lean`
- Full evidence: `logs/relative-filtration-realization-independent-20261009/artifacts.sha256`
