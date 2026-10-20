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
vanish. The original maps and normalization are retained. Nonconnective
completion uses the separate geometric Bass construction, whose direct
TT realization and original Theorem 7.4 are recorded in the
[tensor Bass guide](../../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorBassConstruction.md). The
[geometric completion](../../../AlgebraicGeometry/PerfectComplexes/BoundedFlat/BassComparison.md)
and [generic Bass construction](../../../KTheory/Bass/README.md) own their
distinct finite-stage, fine-range and telescope interfaces.

## Independently varying weak and isomorphism families

[`SimplexReverseMixedWeakProduct`](SimplexReverseMixedWeakProduct.lean) constructs
`ReverseMixedWeakProduct.simplex S G₀ G σ` for a weak model simplex
`S : ModelSimplex W T p` and source arrows `G : Fin (q + 1) → (V ⟶ W)`
anchored by `σ i : G₀.functor ≅ (G i).functor`. Composition runs the source
isomorphism family first and the weak family second. The lexicographic grid
still places the weak coordinate first, so it never inverts a weak transformation.
Every monotone grid face, including each whole row and column, is the literal
diagonal composite of the original restricted diagrams.

[`RealizationReverseMixedWeakProduct`](RealizationReverseMixedWeakProduct.lean)
proves `prespectrum_comp` at every original prespectrum level, including its
level-zero loop input. Its parameter is the original
`SimplexGrid.parameter p q (weakParameter, isoParameter)`: compatibility with
source-first composition follows from the actual simplicial product symmetry
and the original realization-product comparison. No affine-product formula or
definitional transposition is assumed. `prespectrum_row` and `prespectrum_column`
retain the full original families on all grid boundaries. The opposite order
is supplied by [`RealizationMixedWeakProduct`](RealizationMixedWeakProduct.lean).
These two results do not assert a general product producer for two weak families.

### Exact weak-zero product collapse

`MixedWeakZeroGrid` identifies the entire mixed weak-edge/isomorphism Model diagram
with the ordered face of its finite weak-zero normalization simplex. The collapse keeps
the original reference vertex separate and retains every full postwhiskered anchor.
`native` and `native_null` recover the actual realization-product family and its original
reversed weak-null time, including independent level-zero loop inputs. The pure
`Topology/Realization/SimplexWeakZeroGrid` parameter preserves both entire zero/nonzero
rows. It is the image of the genuine realization-product parameter; no equality with an
independently selected affine-cone interior, or completion of the localization overlap
cube, follows from this result.

[`ReverseMixedWeakZeroGrid`](ReverseMixedWeakZeroGrid.lean) supplies the opposite
source-first direction for an actual weak edge `zeroHom W T → F` and source
isomorphism nodes `G_j : V → W`. Its full diagram equality uses the original
`zero_precomp` transport, the prewhiskered transformation `preZero η G₀`, and
complete anchors `isoWhiskerRight (τ j) F.functor`. At the same genuine grid
parameter, `native_null` is the original reversed weak transformation applied
*after* the entire independent source isomorphism family. This also retains the
original loop input at level zero; it does not identify an affine interior or
supply any remaining localization overlap filler.

### Comparing the actual weak-zero product with the affine cone

`WeakZeroProductConeParameter` proves the four whole common boundaries of the
actual collapsed product parameter and the separately specified affine cone.
Its explicit interpolation compares these interiors without identifying them.
`MixedWeakZeroProductConeComparison` and `ReverseMixedWeakZeroProductConeComparison`
realize all six complete faces in the two composition orders, retaining the
original reversed null clock, independently specified endpoint weak-zero maps,
pointedness, and independent structure time. The local comparison does not yet
supply the localization overlap cube of the separately prescribed raw
point-set implementation: that still needs its selected binary/triple/pasting
surfaces embedded in a single full common Model diagram. This raw comparison
is separate from the direct tensor/Bass proof of original TT 7.4 above.

### Exact values of the original binary triangle

[OriginalTriangleSurfaceValue](OriginalTriangleSurfaceValue.lean) proves that
`originalCompositionTransport` preserves every value of the original
transformation-composition surface. Its hypotheses are the original exact
functors, chosen-zero equations, weak transformations and their composition
equality. Both scalar times, every level and every original input remain free.
