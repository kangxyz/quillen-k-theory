# Laurent chart algebra

The original polynomial-to-Laurent maps, variable inversion, coefficient
augmentation and residue are retained over arbitrary commutative rings,
including nonreduced and zero rings. `Cech` proves the signed two-chart kernel,
surjectivity and split-sequence formulas; `Pullback` gives the literal constant
ring pullback, and `Diagonal` identifies the stated quotient kernel.

[`Aglib.Algebra.Polynomial.Laurent.Cutoff`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/Cutoff.lean) and
[`Aglib.Algebra.Polynomial.Laurent.MatrixCutoff`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixCutoff.lean) give uniform finite coefficient windows. The matrix,
projector and module Čech interfaces preserve the supplied transition matrices,
idempotents and scalar-extension units, including both finite-defect
factorizations. Geometric chart realization is a separate consumer.
`Flat` uses the canonical Aglib polynomial/Laurent coefficient pushouts.

`UnderZero` gives literal zero evaluation in the category of algebras under an arbitrary
commutative ring, its naturality, and its retraction of the coefficient inclusion. Its current
consumer is the original coefficient Bass common-corner map. The intended upstream owner is
`Aglib.Algebra.Polynomial.Laurent.UnderZero`.

Native source owners are [`Aglib.Algebra.Polynomial.Laurent.MatrixCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixCech.lean),
[`Aglib.Algebra.Polynomial.Laurent.MatrixProjector`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/MatrixProjector.lean),
[`Aglib.Algebra.Polynomial.Laurent.ProjectorCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ProjectorCech.lean),
[`Aglib.Algebra.Polynomial.Laurent.ProjectorFiniteDefects`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ProjectorFiniteDefects.lean), and
[`Aglib.Algebra.Polynomial.Laurent.ModuleCech`](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/Algebra/Polynomial/Laurent/ModuleCech.lean).
Cutoff declarations use `LaurentPolynomial.Cutoff`, projector declarations use
`LaurentPolynomial.Projector`, and module chart declarations use
`ModuleCat.LaurentCech`. Local ordinary Laurent algebra remains in its existing
source leaves.
