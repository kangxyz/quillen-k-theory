# Regular-local projective dimension

`PrincipalDomain` treats a noetherian local ring with principal maximal ideal:
Krull intersection gives the stated power-times-unit factorization, and
positive dimension gives the domain property. `LowDimension` retains the
regular dimension-at-most-one PID corollaries, using the canonical Aglib
regular-domain theorem for the existing domain corollary.

`QuotientLifting` requires the specified regular scalar on both ring and
module and a projective-dimension bound after quotienting. `ProjectiveDimension`
then proves the stated regular-local dimension bound using the actual regular
parameter and finite-free syzygies. The module objects and Ext-defined
projective-dimension conditions are unchanged.

`GlobalProjectiveDimension` gives an object-dependent finite bound from finite
projective dimension at every prime localization, without asserting a uniform
bound for the ring. The scheme-origin `AffineProjectiveDimension` separately
retains the PID bound one, the regular dimension-at-most-one bound one, and a
specified finite dimension bound for all finite modules. These are algebraic
module statements; geometric K/G-theory comparisons remain downstream.

## Regular local coefficient foundation

The actual integral regular system is the free module on path classes from a
chosen basepoint. Transport is postcomposition; inverse-path transport is
proved and basepoint monodromy is faithful without an abelian hypothesis.
`RegularGroupRing` identifies the fiber with the integral group ring on the
original first homotopy group. Under Mathlib's multiplication convention the
transport formula is left multiplication. `CoefficientLift` and
`RegularUniverseLift` put these coefficients in a displayed sufficient universe
and preserve path transport and faithful monodromy.
[`Consumer.RegularLocalCoefficients`](../../../../examples/downstream/Consumer/RegularLocalCoefficients.lean)
checks commutation detection, orientation and inverse lifted transport.

These regular systems support the simply-connected homological weak Whitehead
and supplied-cover twisted Whitehead theorems. Actual metric realization and
loop geometry also construct the domination used in the exact original-Q
comparison above. See the [foundations guide](../../../../docs/topics/HomotopyFoundations.md) for their
hypotheses, original maps and covering boundary.
