# Signed permutation sections

`Basic.lean` contains prefix-inversion counts, literal column matrices and their
explicit inverses, and the ascent/descent recurrence for `Wminus`. It works over
an arbitrary field and finite index rank, with each recurrence retaining its
stated ascent or descent comparison. It uses the displayed column convention;
no alternate permutation-matrix convention is substituted.

The native namespace is `Matrix.GeneralLinearGroup.SignedSection`; the intended
upstream owner is `Aglib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection.Basic`.
The current consumer is the root-coordinate section bridge and actual
normalizer matrix projection in the Matsumoto `NormalizerMatrix` provider.
