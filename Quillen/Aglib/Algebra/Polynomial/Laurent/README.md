# Laurent chart algebra

The original polynomial-to-Laurent maps, variable inversion, coefficient
augmentation and residue are retained over arbitrary commutative rings,
including nonreduced and zero rings. `Cech` proves the signed two-chart kernel,
surjectivity and split-sequence formulas; `Pullback` gives the literal constant
ring pullback, and `Diagonal` identifies the stated quotient kernel.

`Cutoff` and `MatrixCutoff` give uniform finite coefficient windows. The matrix,
projector and module Čech interfaces preserve the supplied transition matrices,
idempotents and scalar-extension units, including both finite-defect
factorizations. Geometric chart realization is a separate consumer.
`Flat` uses the canonical Aglib polynomial/Laurent coefficient pushouts.

`UnderZero` gives literal zero evaluation in the category of algebras under an arbitrary
commutative ring, its naturality, and its retraction of the coefficient inclusion. Its current
consumer is the original coefficient Bass common-corner map. The intended upstream owner is
`Aglib.Algebra.Polynomial.Laurent.UnderZero`.
