# Affine candidates

These leaves compare actual affine global sections, injective complexes and injective resolutions, prove the original tilde Ext comparison, and give finite principal-cover bounds on section complexes. Quasicoherence, boundedness and finite-cover assumptions remain explicit in each result.

These local general-theory candidates preserve the existing declaration namespaces, hypotheses and universes. Their K-theory applications remain in downstream modules.

- [`ExtComparison.lean`](ExtComparison.lean)
- [`FinitePrincipalDimension.lean`](FinitePrincipalDimension.lean)
- [`InjectiveComplex.lean`](InjectiveComplex.lean)

Injective resolutions and their original sections augmentations now come directly from
`Aglib.AlgebraicGeometry.Cohomology.Affine.InjectiveResolution`. The local copied leaf is
retired; callers use `globalSectionsInjectiveResolution (M := M) I` and
`globalSectionsAugmentation I`, retaining the supplied resolution and its mapped complex.
