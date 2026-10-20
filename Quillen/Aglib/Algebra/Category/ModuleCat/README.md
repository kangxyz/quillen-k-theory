# Module-category scalar extension interfaces

## Imports

| Import | Interface |
| --- | --- |
| `Quillen.Aglib.Algebra.Category.ModuleCat.RightScalarExtension` | Tensor functor, identity/composition equivalences and literal-carrier triple coherence |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeTensor` | Comparison with original scalar extension and explicit target lifts |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveTensorCoherence` | Agreement with original identity/composition comparisons |
| `Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal` | Scalar-extension unit and additive Hom universal property |


## Scalar base-change transformation

`ModuleCat.scalarBaseChangeNatTrans` and `scalarBaseChangeNatTrans_unit` retain
the whole candidate natural transformation and its actual unit equation.
They are distinct from Aglib's per-module `scalarBaseChangeMap`; no component
comparison with that native API is asserted. The local
[`CartesianBaseChange`](CartesianBaseChange.lean) leaf additionally proves
`scalarBaseChangeMap_eq_isoApp`, the pure-tensor formula and invertibility
of this natural transformation for an actual ring pushout, without flatness
or finite-generation assumptions. `Consumer.PublicLibraries` imports both public roots.
