# Scalar automorphisms

[ScalarAutomorphism.lean](ScalarAutomorphism.lean) is a candidate for
`Aglib.CategoryTheory.Linear.ScalarAutomorphism`. Its current consumer is
[ScalarUnit](../../../KTheory/LowDegreeScalarAction/ScalarUnit.lean).

For a ring `R` and an `R`-linear preadditive category `C`, `scalarNatAut`
composes the category-center map with the existing units-to-automorphisms
equivalence. Its components are `(r : R) • 𝟙 X`; inverse components use the
inverse unit. Ordinary `R`-linear functors preserve these components.

When `C` is essentially small, `smallModelScalarNatAut` lifts the same
scalar automorphism through the original chosen-model realization using full
faithfulness. The realization and chosen-model functor equations retain that
original scalar. No linear structure on the model or K-theory data is required.
