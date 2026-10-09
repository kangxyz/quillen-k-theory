# The canonical comparison through the original all-weak fiber

`Fibration/AllWeak/CanonicalFiberFactorization.lean` builds the literal lift
from W.Delooping into the actual homotopy fiber of the original
change-of-weak map W → AllWeak(W). The source coordinate remains x; its path
is exactly the original all-weak contraction applied to the original image
of x. Projection composed with this lift is strictly identity.

The target all-weak delooping has the already proved actual contraction.
The accepted contracted-base projection equivalence and ordinary homotopy-
equivalence cancellation therefore prove a genuine homotopy equivalence
whose forward map is this exact lift and whose inverse is the original
fiber projection. Its actual chosen basepoint and bijectivity on every
finite based homotopy degree, including degree zero, are retained.

For a nested weak structure N with coarse two-out-of-three, the actual fine
acyclic inclusion and its all-weak-source coarse inclusion give the original
strict square of change-of-weak maps. `acyclicFiberSquareMap N` applies the
original fine inclusion to the source coordinate and the original coarse
inclusion to the entire path. The proved chosen-zero equality places it in
the original target fiber, with no change of basepoint by a chosen path.

The theorem `acyclicFiberSquareMap_changeWeakFiberLift` proves that its
composite with the genuine contraction lift is exactly `canonicalFiberMap N`.
The proof uses the complete original nullhomotopy identity, including every
intermediate path point and its reversal. All constructions retain arbitrary
independent category object and hom universes. No extension, cylinder,
projectivity or finite-bound hypothesis is added.

This is an actual map factorization and a genuine equivalence for its first
factor. It does not establish a homotopy-cartesian square or an equivalence
for `acyclicFiberSquareMap N`; the global relative fiber theorem and that
remaining comparison remain separate substantive obligations.

The focused source check passed warning-free. The combined source manifest
is `logs/all-weak-fiber-square-sources.sha256`; the single-pass recursive
origin audit with original-map, whole-path, inverse, degree-zero and
arbitrary-scheme consumers is in `audits/AllWeakFiberSquareAudit.lean`. The final fixed41 audit
([20,21]) and all31 consumers passed warning-free in
`logs/all-weak-fiber-square-audit-final.log`.
Independent fresh2/fixed41/37-consumer review is accepted; see
`docs/REVIEW_20261009_ALL_WEAK_FIBER_SQUARE.md`.
