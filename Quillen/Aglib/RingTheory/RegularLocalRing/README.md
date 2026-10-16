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
