# Module constructions

`FiniteCoefficientRetract` constructs the actual retraction onto a finite
coefficient window when the split inclusion lands there; finite support alone
is insufficient over an arbitrary ring. `FiniteParametrix` constructs a finite
projective split kernel from the displayed finite defect factorizations and
projectivity hypotheses, without assuming Noetherianity.

`MatrixPresentation` realizes finite projective modules as actual idempotent
matrix images. `MatrixBaseChange` retains their original splittings and the
coefficientwise matrix map, without a flatness hypothesis. `RightScalarExtension`
constructs balanced tensor extension for arbitrary unital rings using its
balanced biadditive universal property, preserving the order of multiplication.

These are ordinary module interfaces. Stable matrix classes and K-theory maps
remain downstream. The source modules retain their existing namespaces.
