import Quillen.Scheme.Regular.SmallComparison
import Quillen.Scheme.Regular.Field
import Quillen.Scheme.Regular.AffineLowDimension
import Quillen.Scheme.Regular.AffineFiniteDimension
import Quillen.Scheme.Regular.Affine
import Quillen.Scheme.Regular.GlobalComparison

/-!
# Checked canonical regular K-to-G equivalences

`Scheme.KToGRegularAffineEquiv` proves the original canonical K-to-G comparison
for every regular affine ring, with no finite Krull-dimension bound. PID,
field and finite-dimensional specializations remain available. Every forward
homomorphism is exactly the existing `Scheme.KToG`.
`Scheme.KToGRegularEquiv` also proves the canonical comparison for every
quasi-compact regular scheme with the ordinary resolution property. Its
finite resolutions are derived, without a global dimension bound.
-/
