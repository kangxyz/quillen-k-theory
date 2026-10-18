# GilletWaldhausen interfaces

## Bounded complexes and Gillet–Waldhausen

The general comparison takes `A : Type (max u v)` with `[Category.{v} A]` and
`[Abelian A]`. Its term property `P` has `[P.ContainsZero]`,
`[P.IsClosedUnderIsomorphisms]`, and
`[(Quillen.abelianExactStructure A).IsExtensionClosed P]`.
[`boundedTerms P`](../../Aglib/Algebra/Homology/CochainComplex/ExactSubcategory/BoundedTerms.lean)
consists of term-bounded cochain complexes with every term in `P`. The
[nested models](FibrationModels.lean)
share inherited admissible cofibrations and zero, with fine isomorphisms and
coarse quasi-isomorphisms.

`GilletWaldhausen.boundedTermsSingleCoarseKEquivGeneral P n` additionally requires
`[(Quillen.abelianExactStructure A).IsKernelClosed P]`. This is
[admissible kernel closure](../../Resolution/Finite.lean): membership of the
middle and quotient of a conflation implies membership of the kernel, without
arbitrary admissible-subobject closure. The equivalence goes from the term category's
isomorphism-weak S-model to `(boundedTermsNested P).coarse.K n`, including `n = 0`,
with `KMap (boundedTermsSingle_coarseExact P 0) n` forward. This inserts the original
term as a single complex in cochain degree zero. The bounded-complex cylinder and
section data are constructed under these conditions.
