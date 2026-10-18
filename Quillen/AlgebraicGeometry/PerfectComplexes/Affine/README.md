# Affine Bass steps and quotient-graded sections

The affine raw step, fine full-open section model, and quotient-graded model have different weak classes and comparison maps. The constructions below retain the original Laurent unit, chosen pullback opens, and whole localization null. [Bounded-flat comparisons](../BoundedFlat/BassComparison.md) give the global and finite-stage interfaces; [comparison boundaries](../Development.md) record the classical TT gap.

## Objects and conventions

The raw spectral step `affineBassStep R` is the parameter-looped cone of the
actual two-polynomial-chart comparison to the Laurent corner.
[`affineBassTransition`](BassStep.lean)
uses the original Laurent-unit track and cone nullhomotopy. The bounded-flat
and perfect raw steps have the original comparison
`boundedFlatPerfectGeometricBassStepMap`, completely weak at positive levels
and stable in every integer degree.

## The quotient-graded full-open Bass telescope

Fix `R : CommRingCat.{u}` and an open immersion `j : U ⟶ Spec R`.
The full-open section model at `a : Under R` evaluates on the specified
pullback open `openSpace j a`. Its quotient grading is the raw-perfect K₀ class
modulo the image of the original relative-open restriction. Grade equality
coarsens weak equivalences while retaining the original objects, cofibrations,
and chosen zero. These Models and their spectra lie in universe `u+1`.
The pointwise restriction Model map preserves the whole chosen zero section
literally. The geometric definitions and restriction comparison are described
in [perfect-complex guide](../README.md).

For every such open `j`, the initial graded Model has zero stable groups in
degrees `d ≠ 0`, without a compactness assumption. The independent client
[`Consumer.FullOpenGradedSectionStable`](../../../../examples/downstream/Consumer/FullOpenGradedSectionStable.lean)
uses this concentration to prove that any supplied map between the actual
graded Models induces an isomorphism in nonzero degree. It constructs no
missing comparison and asserts no degree-zero isomorphism.

With `[CompactSpace U]`, the actual coefficient diagram, Laurent seed, natural
contraction, and Bass telescope are defined over `Under R`, with arbitrary
coefficient arrows. No flatness, regularity, noetherian condition, or affineness
of `U` is imposed. The original forward Laurent self-track has a whole relative
contraction to the constant track of the same coefficient map.
[`FullOpenGradedLaurentContractionNaturality`](FullOpenGradedLaurentContractionNaturality.lean)
retains the exact Model-square transports and independent comparison, action,
and structure coordinates, including the level-zero internal loop coordinate.

Cone inclusion and conjugation by the original source-leg cone null produce
`boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull`, a constructed
coefficient-natural whole null of the actual graded seed.
[`strictDiagramIterateNull`](../../../KTheory/Bass/StrictDiagramIterateNull.lean)
transports this same null through the existing Bass action and successor
isomorphisms. `boundedFlatAffineFullOpenGradedSectionBassTransition_stableMap_eq_zero`
therefore gives zero for every original finite transition at every `a : Under R`
and every `d : ℤ`.

The actual reduced telescope is
`boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor`.
[`boundedFlatAffineFullOpenGradedSectionBassTelescope_stableGroup_subsingleton`](FullOpenGradedSectionBassTelescope.lean)
gives vanishing of its stable group for every coefficient `a` and every integer
degree `d`. Each original stage inclusion factors on stable groups through its
zero next transition, and T1 finite-stage representability accounts for every
telescope class. Initial graded concentration and individual-stage vanishing
are not premises of this argument; no seed-null premise is supplied.

Writing `seedFine` and `seedGraded` for the two actual seed transformations,
and `q` for the fine-to-graded transformation, the exact equation
`seedFine ≫ B.map(q) = q ≫ seedGraded` is already proved in
[`FullOpenSectionBassSeedChangeWeak`](FullOpenSectionBassSeedChangeWeak.lean).
The actual fine tower and telescope, and the induced finite/telescope q maps,
are constructed in `FullOpenSectionBassTower`, `FullOpenSectionBassTelescope`,
`FullOpenSectionBassGradingTower` and `FullOpenSectionBassGradingTelescope`.
The original r coefficient transformation and canonical whole localization
null are constructed; `FullOpenSectionConeStable` proves its initial cone descent
stable in every integer degree, including the honest degree-zero image quotient.
`FullOpenSectionBassRestrictionTower` iterates the same null and stable cone
comparison through every actual finite stage.

The original r seed square and canonical-null time-slice seed squares are proved
in `FullOpenSectionRestrictionSeed` and `FullOpenSectionGradingNullBassSeed`.
`FullOpenSectionBassRestrictionCofiber` retains the actual finite nulls and their
transition equations in the telescope. Its original cone descent is stable;
graded signed vanishing and genuine finite Model excision therefore make the
same r∞ stable in every integer degree. `FullOpenSectionBassLocalization`
composes the supported coarse cone comparison with this restriction, giving
the actual fine completion endpoint, the same whole-null fiber lift and the
original signed connecting identity. Pointwise fine section evaluation is
stable with its explicit universe lift and chosen-zero normalization;
evaluation through the seeds, iterates and telescope remains separate.
See the [TT localization roadmap](../Development.md).

For the fine ambient and supported telescopes, the original-group
identifications and finite-stage ranges are now supplied under the hypotheses
above. Full all-iterate comparison with the original raw geometric towers and
classical nonconnective identification remain open. Native global C/F/G Models now have
their original Laurent seeds, canonical nulls, actual finite/telescope maps and
graded contraction. The original coarse-to-fine completion restriction is
stable for qcqs ambient schemes and quasi-compact opens. Basic global supported
completion now has the actual cone and same-null stable fiber comparison, with
its original signed boundary. Auxiliary-supported cofinality, honest K₀
exactness and the initial signed cone are proved. Their original supported
seeds, whole null-transition equations, finite/telescope maps and stable r_Z∞
are constructed. The native auxiliary fiber-forget localization now has
its actual union-support fiber, original seed/whole-null transfer and telescope
cone/fiber comparison, including the signed boundary. Final fine stability
requires compact P,Q,T and quasi-separated Q; the structural identities and
fiber-to-coarse stability need only the open immersion. The older raw-cell
evaluation route and classical nonconnective Thomason–Trobaugh identification
retain their separate boundaries. The native basic-pair current-stage theorem
is described above.
The connective S-spectrum comparison does not settle these questions.
The conditional `Bass.TwoChartStableSpan` and `TwoChartStableSequence` now
provide the signed span quotient, natural all-degree Bass short exact row,
and actual cycles/image right-term identification. Their original plus
retraction and cone/collapse stability inputs are realized for the actual
finite coefficient Models by `CoefficientTwoChartStableSequence`. The original
ambient and supported middle rows, connective seeds and full fine transition
ranges have their additional geometric proofs; the generic structural
interface alone does not imply them.
See [scope summary](../../../../docs/SCOPE.md) for the global frontier and
[recorded evidence](../../../../docs/evidence/README.md#affine-supported-construction-record)
for historical source and validation scope.

## Actual affine coefficient objects

Fix `R : CommRingCat.{u}`, `j : U ⟶ Spec R` with `[IsOpenImmersion j]`.
Coefficients are arbitrary `a : Under R`, with arbitrary coefficient arrows.
Retain `[CompactSpace U]` for quotient grading and the initial full-open stable
comparison; add no flatness, noetherian, regularity or affineness assumption on U.
Models and prespectra are in universe `u + 1`.

| Symbol | Actual source object |
| --- | --- |
| `C` | `boundedFlatAffineSectionOpenPrespectrumFunctor j`, coarse relative-open sections |
| `F` | `boundedFlatAffineFullOpenSectionPrespectrumFunctor j`, fine full-open sections |
| `G` | `boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j`, quotient-graded sections |
| `rₐ` | `prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a)` |
| `q` | `boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j` |

`q` is not asserted to be a stable equivalence. The required comparison is

```text
Cone(rₐ) → G(a), using a constructed null Nₐ of rₐ ≫ qₐ.
```

The chosen coefficient pullback open remains `openSpace j a`. At the identity
algebra it is related to U by the original projection isomorphism; it is not
silently replaced by a definitionally equal open.

## Source interfaces

| Source / interface | Description |
| --- | --- |
| `AlgebraicGeometry.PerfectComplexes.Affine.SectionBassNegativeMap` | Finite-stage bottom comparison and natural negative-class maps |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedLaurentContractionNaturality` | Whole Laurent self-track contraction and coefficient naturality |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedDiagramNull` | Constructed natural nullhomotopy of the original graded Bass seed |
| `AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTelescope` | All-integer transition-zero and actual graded telescope stable-group vanishing |
