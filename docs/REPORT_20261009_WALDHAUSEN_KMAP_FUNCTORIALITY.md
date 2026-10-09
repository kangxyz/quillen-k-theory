# Original Waldhausen K-map functoriality

Import `Quillen.Waldhausen.Functoriality.KMap`.

## Checked public API

In `Quillen.Waldhausen`, for genuine exact functors between Waldhausen
structures with arbitrary common object/hom universe levels:

- `KMap_eq_of_weakNatTrans`: a pointwise weak natural transformation induces
  equality of the original canonical chosen-zero K-maps.
- `KMap_eq_of_iso`: the natural-isomorphism specialization.
- `KMap_eq_piMap_of_zeroEq`: a strictly zero-preserving original functor's
  K-map is exactly its original realization map on the based homotopy group.
- `KMap_id` and `KMap_comp`: actual identity and composition laws.
- `zeroFunctor`, `zeroFunctor_isExact`, and `KMap_zeroFunctor`: the actual
  chosen-zero constant functor is exact and induces the trivial homomorphism.
- `sSetMap_id/comp`, `deloopingMap_id/comp`, and the zero-functor formulas
  retain the literal original simplicial and realization maps.

All degrees include `n = 0`. The invariance theorems do not require strict
zero preservation or a transformation component identity as a hypothesis.
The actual natural transformation is conjugated by the original canonical
zero normalizations. Both normalized endpoints have the same chosen zero,
so the previously proved weak nerve-cylinder theorem gives a genuinely
fixed-zero realization homotopy.

This companion imports the original pointed functor and weak-natural-
transformation infrastructure independently of the additivity modules.

## Validation

The source is frozen in `logs/waldhausen-kmap-functoriality-sources.sha256`.
Its focused check produced an importable output with no warnings.
`audits/WaldhausenKMapFunctorialityAudit.lean` asserts the fixed count of
**22** defining-module declarations and recursively checks that only
`propext`, `Classical.choice`, and `Quot.sound` occur as axioms.

Arbitrary-universe consumers cover pointwise weak transformations,
composition, degree-zero identity, zero functors, and the exact original
realization formula. Actual bounded-acyclic consumers use the proved
fixed-bound truncation natural isomorphisms: below the lower bound the
restricted truncation K-map is trivial; above the upper bound it equals the
actual stratum inclusion K-map. No vanishing assertion for the acyclic
inclusion is made.

The fixed-count audit and consumers passed warning-free. Its output is
`logs/waldhausen-kmap-functoriality-fixed-audit.log`, extracted from the
completed first command of the preserved serial log
`logs/waldhausen-kmap-fixed-audit-serial-raw.log`. The later command's
unrelated initial K-equivalence elaboration error is retained in that raw
log; the shell's `&&` sequencing records that the audit itself exited zero.
The earlier standalone successful audit is also retained as
`logs/waldhausen-kmap-functoriality-audit.log`.

Independent source review and acceptance are maintained by the coordinator.
