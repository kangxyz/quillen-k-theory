# Finite matrix Bruhat providers

The native namespace is `Matrix.Bruhat`. These candidates concern arbitrary
fields, literal finite matrix units, diagonal/permutation coordinates and
upper-unipotent factors. `Coordinates` contains only the selected ordinary
permutation action, its semidirect product, final-index permutation extension,
monomial matrices and upper-factor matrix lemmas. It contains no Milnor-valued
old-model extension or sorting correction.

`Decomposition` proves the selected finite decomposition and monomial-factor
projection. `RootUpdate` treats the two literal elementary-root update branches.
`Opposite` and `Distinct` retain their explicit index, sign, pivot, nonzero and
branch hypotheses for rank-two comparisons; `Reduction` supplies the finite
four-monomial reduction with its stated upper factors. No branch hypothesis is
removed by this relocation.

The intended upstream modules mirror these leaves under
`Aglib.LinearAlgebra.Matrix.Bruhat`. The current consumers are the actual
root-coordinate Bruhat action, reduction, distinct and opposite/equal coherence
providers in `Quillen.Algebra.Group.StableSteinberg.Matsumoto`.

Only source commands selected by the accepted declaration closure and any
separately released elaboration dependencies are enrolled. The historical mixed
supplier modules are not compatibility imports. Existing finite GL and
stabilization objects retain their precise declaration origin
`Quillen.Aglib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization` and their
existing public names.
