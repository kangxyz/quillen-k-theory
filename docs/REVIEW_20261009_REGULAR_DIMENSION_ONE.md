# Independent review: canonical regular affine comparison in dimension at most one

The integration reviewer inspected `LocalPrincipalDomain`, `LocalLowDimension`, and `AffineLowDimension` separately from their proof author.

## Exact endpoint

For a commutative ring object `R`, mathlib's actual `IsRegularRing R`, and `ringKrullDim R ≤ 1`, `Scheme.KToG_regular_dimension_le_one_bijective` proves bijectivity of the existing canonical `Scheme.KToG (Spec R) n` for every nonnegative degree. `KToGRegularDimOneEquiv` has exactly that homomorphism as forward map, by reflexivity. No domain, PID, projective-dimension, chosen-resolution, or desired-equivalence hypothesis is supplied by the caller.

## Proof inspected

1. Krull intersection supplies a final maximal-ideal power containing any nonzero element. A principal maximal ideal therefore gives the actual expression πⁿ times a unit.
2. A nilpotent generator would make every prime maximal and force Krull dimension zero. Consequently positive dimension implies no zero divisors. The domain property is derived, not assumed.
3. Actual regular-local cotangent dimension implies a principal maximal ideal in dimension at most one. The dimension-zero case is a field; the positive-dimensional case is a domain and then a principal ideal ring by mathlib's local equivalence theorem.
4. Finite modules over each prime localization have projective dimension at most one by the already proved finite-free syzygy construction. The genuine local-to-global projective-dimension theorem yields the global bound.
5. Actual finite-projective resolutions are transported to coherent sheaves using the previously independently reviewed affine/module and vector-bundle exact comparisons. The proved length-one resolution theorem applies to the canonical small-model map.

No mathematical correctness blocker was found. This review does not assert the arbitrary higher-dimensional regular-local homological theorem, a global resolution property for arbitrary schemes, or any perfect-complex comparison.

## Reproducibility

The focused persistent build passed 3,386 jobs (`logs/regular-lowdim-build-rehash.log`). The independent module-origin audit, including private/generated declarations and a consumer forward-map example, is `audits/RegularLowDimensionIndependentAudit.lean`. Its result and unchanged-source fingerprint checks are recorded in `logs/regular-lowdim-independent-audit.log` and `logs/regular-lowdim-independent.sha256`.

Independent audit completed successfully: all 66 declarations in the three modules use only `propext`, `Classical.choice`, and `Quot.sound`. The canonical forward-map consumer example compiled, and all three source hashes matched afterward.
