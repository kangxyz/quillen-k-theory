# The original connective iterated S-spectrum

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality` | Iterated S-spectrum, additive K-comparison, and exact-functor laws |

## Spectral and Bass entrypoints

| Import after `Quillen.` | Interface |
| --- | --- |
| `Waldhausen.SConstruction.Iterated.StableHomotopy` | Original additive `originalKStableEquiv` and connective spectrum |
| `Waldhausen.SConstruction.Iterated.StableFunctoriality` | Normalized exact-functor spectrum maps and K-map naturality |
| `Waldhausen.SConstruction.Iterated.LocalizedFunctoriality` | `localizedSpectrumMap` and its strict laws |

## Global sections and finite Bass interchange

| Import after `Quillen.` | Principal interface |
| --- | --- |
| `Waldhausen.SConstruction.Iterated.SectionChangeIndexModel`, `SectionChangeIndexLargeModel`, `SectionChangeIndexMixedModel` | Evaluation-transported `sectionWaldhausen`, `sectionModel`, `restrictionModel` and exact categorical inverse |

## The original connective S-spectrum

[`LoopPrespectrum`](../../../Topology/Prespectrum/Loop.lean) consists of
based spaces `Eₙ` and continuous based structure maps `Eₙ → ΩEₙ₊₁`.
Its morphisms retain the exact structure squares.
For `d : ℤ`, `stableHomotopyGroup E d` is the additive sequential colimit

```text
colim_n π_(d.toNat + n + 2)(E_((-d).toNat + n + 2)),  n : ℕ.
```

These degrees are at least two, so the diagram uses abelian groups throughout.
[`StableHomotopy`](../../../Topology/Prespectrum/StableHomotopy.lean)
defines the original structure-induced transitions and stage inclusions.

`originalPrespectrum W` uses the actual iterated S-construction and its original
cylinder transitions. For `W : Structure C`, where `C : Type u` and
`[Category.{v} C]`, its spaces lie in universe `max u v` through the genuine
small model. [`originalPrespectrum_isOmega`](OmegaSpectrum.lean)
proves complete weakness of the unchanged structure maps. The additive
equivalence `originalKStableEquiv W n` identifies `Additive (W.K n)` with
`stableHomotopyGroup (originalPrespectrum W) (n : ℤ)` for every `n : ℕ`.
The degree-zero comparison retains the group law; the older
`originalZeroSpaceEquiv` is only a set equivalence.
[`originalStableHomotopyGroup_neg_subsingleton`](StableHomotopy.lean)
gives vanishing in every negative degree.

For an arbitrary exact functor, `exactOriginalPrespectrumMap` and
`exactOriginalOmegaSpectrumMap` canonically normalize its value on the chosen
zero. `originalKStableEquiv_exact_naturality` retains the public `KMap`, without
requiring equality of the original zero image.
[`StableFunctoriality`](StableFunctoriality.lean)
gives identity, composition, and weak-natural-transformation laws for
`exactStableKMap`. These original exact-functor statements use source and target
categories in common object universe `u` and common morphism universe `v`;
independence of `u` and `v` does not assert arbitrary cross-universe transport.

The normalized prespectrum maps have whole coherent based identity and
composition homotopies. Their composition tracks come from the genuine
transformation two-simplex, retaining all three cylinder faces.
[`PrespectrumCompositionHomotopy`](PrespectrumCompositionHomotopy.lean)
and the normalization/pasting owners keep comparison, path or loop, and
structure parameters independent, including level-zero loops. Object tracks
also retain their original paths: [`CanonicalFiberObjectLoop`](../../Fibration/CanonicalFiberObjectLoop.lean)
records both fiber coordinates and the reversed zero-to-acyclic track.
For an exact model equivalence, [`ExactModelEquivalence`](ExactModelEquivalence.lean)
retains a zero-preserving forward functor, normalizes its exact inverse, and
constructs whole unit/counit homotopies and levelwise homotopy equivalences.

## Original connective groups

The iterated S-spectrum identifies its nonnegative stable groups with the
original Waldhausen K-groups, including degree zero. Its negative stable groups
vanish. The original maps and normalization are retained; a classical
nonconnective identification is a separate comparison. The
[geometric completion](../../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md)
and [generic Bass construction](../../../KTheory/Bass/README.md) own their
distinct finite-stage, fine-range and telescope interfaces.
