# Regular schemes and the canonical K-to-G map

## Regular K-to-G comparison

For `[IsRegularRing R]`, `KToG_regular_affine_bijective R n` and
`KToGRegularAffineEquiv R n` cover every nonnegative degree on `Spec R`, with
the original `KToG` as forward map. The proof constructs actual finite
vector-bundle resolutions from objectwise finite projective dimension.
There is no finite Krull-dimension restriction or common resolution bound.
PID and dimension-at-most-one specializations remain in `Scheme.Regular`.

`AlgebraicGeometry.Scheme.IsRegular X` is local noetherianity with regular local stalks.
For a nonaffine scheme, `KToGRegularEquiv X n` requires this regularity,
`[CompactSpace X]` (quasi-compactness), and `[HasResolutionProperty X]`.
The resolution property says that every coherent sheaf is an actual quotient
of a finite locally free sheaf. It supplies coherent syzygies; the regular,
quasi-compact argument produces the finite resolutions needed by
[Quillen resolution](../../../Resolution/README.md).
Regularity alone does not supply the resolution property.

`KToGRegularEquiv_coe` retains the canonical comparison, and
`KToGRegularEquiv_spec` identifies its affine specialization with the
independently constructed regular-affine equivalence. The more general
`AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_finite_resolutions` retains its admissible
kernel-closure and actual finite-resolution premises.

## General prerequisites

The current general interfaces are
[`FiniteProjectiveResolution`](../../../Aglib/Algebra/Homology/ModuleCat/FiniteProjectiveResolution.lean)
and [`PrincipalDomain`](../../../Aglib/RingTheory/RegularLocalRing/PrincipalDomain.lean).
Their regular-scheme applications retain the hypotheses above.
