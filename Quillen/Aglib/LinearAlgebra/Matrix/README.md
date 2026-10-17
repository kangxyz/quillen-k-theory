# Finite matrix foundations

These candidates work over arbitrary rings, including noncommutative and zero
rings, with no invariant-basis-number hypothesis. Elementary units, their
Steinberg relation, reindexing and Whitehead block factorization retain the
actual finite matrices.

`RightLinear`, `RightScalarExtension` and the automorphism files identify the
original right-module column actions and retain their finite-free direct-sum
coordinates. `GeneralLinearGroup/Stabilization` contains only the finite
matrix-unit groups, finite-rank transitions and entrywise ring maps.
`ElementaryStabilization` and `BlockOperations` keep the original elementary
coordinates, permutation units, block swaps and rectangular involutions.

The historical declaration namespaces are preserved during this structural
relocation. The stable direct-limit group, stable elementary quotient and
automorphism classes remain downstream. Matrix-summand automorphisms and
retract presentations are under `Algebra/Category/ModuleCat/MatrixAutomorphisms`.
