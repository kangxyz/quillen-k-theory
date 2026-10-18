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

## Matrix reduction and branch coverage

For the actual matrix `g` with monomial factor `m = v(g)`, the reduction gives
upper-unitriangular remainders `U0,V0` and parameters `u,v` such that
`g = U0 * (X_i(u) * M(m) * X_k(v)) * V0`, with the two relevant adjacent
entries zero. The signed-Weyl conjugates of the remainders remain upper
unitriangular. The same witnesses therefore preserve the original monomial
factors of `g`, `W_i(1)g`, `gW_k(-1)` and `W_i(1)gW_k(-1)`.
Zero parameters, equal indices and characteristic two add no hypothesis.
The opposite-root branch separately covers zero and vanishing crossing
denominators; a nondegenerate symbol identity alone does not cover these cases.

This is pure matrix geometry over every field. The Milnor-valued faithful
normalizer and the full lifted left/right state actions have their authority in
the [Matsumoto construction](../../../../Algebra/Group/StableSteinberg/Matsumoto/README.md#lifted-bruhat-states-and-the-complete-extension).
