# Ordinary twofold subdivision realization

The four sources listed in `logs/ordinal-subdivision-sources.sha256` are frozen.
They define the ordinary indexing functor `[n] ↦ [n] ⋆ [n]`, with the same
ordinal map on both halves and no reversal, and prove that its canonical
first-half endpoint realizes to a homotopy equivalence for every simplicial set.

## Exact interfaces

All declarations are in `Quillen.OrdinalSubdivision`.

- `δ`, `first`, `second`, `subdivision`, `subdivisionFunctor`, `endpoint`,
  `endpointNatTrans` give the actual indexing and restriction maps.
- `contractibleSpace_simplex` contracts each subdivided standard simplex using
  two explicit, ordinal-natural simplicial homotopies: first collapse the first
  half, then collapse the second half. The realized homotopies are concatenated.
- `realizationHomotopyEquiv X` has forward map definitionally equal to
  `(SSet.toTop.map (endpoint X)).hom`. Naturality and preservation of the original
  chosen vertex are proved.
- `horizontalRealizationHomotopyEquiv X` compares the diagonal of `δ.op ⋙ X`
  to the original bisimplicial diagonal. Its forward map is exactly realization
  of `TheoremA.diagonalMap (horizontalEndpoint X)`.
- `firstIndexRealizationHomotopyEquiv X` compares double subdivision with
  outer-only subdivision by the actual inner first-half restriction.

The global realization theorem uses the previously checked skeletal cellular
criterion, including monomorphism homotopy extension and sequential gluing.
The partial bisimplicial bridge uses genuine adjacent-composite two-out-of-six.
No compatible inverse choices, finite-dimensional assumption, homeomorphism,
or desired comparison conclusion is supplied as a hypothesis.

## Checks

All four implementation sources compiled warning-free under Lean 4.34.0 using
direct focused checks. `audits/OrdinalSubdivisionAudit.lean` recursively checks
all 89 declaration origins from these four modules, including private/generated
declarations, against only `propext`, `Classical.choice`, and `Quot.sound`.
The count-frozen rerun passed. Arbitrary-universe consumer examples check the
non-reversed map, exact forward maps, naturality, chosen vertex, representable
contractibility, and partial bisimplicial endpoints. All source hashes match.

This scope supplies ordinary subdivision, not yet the variable-suffix mixed
ordinal cylinder needed by the subsequent explicit additivity deformation.
