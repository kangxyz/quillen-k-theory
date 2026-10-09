# Generic rowwise-to-diagonal realization equivalence

## Exact endpoint

Import `Quillen.Topology.Realization.BisimplicialEquivalence`.
In namespace `Quillen.BisimplicialRealization`, for arbitrary bisimplicial
sets `X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}` and a map `η : X ⟶ Y`:

```
diagonalRealizationHomotopyEquiv η
  (e : ∀ n, ContinuousMap.HomotopyEquiv
    |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
  (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom) :
  ContinuousMap.HomotopyEquiv
    |Quillen.TheoremA.diagonalSSet X| |Quillen.TheoremA.diagonalSSet Y|
```

`diagonalRealizationHomotopyEquiv_toFun` identifies the forward map,
definitionally, with the realization of `TheoremA.diagonalMap η`.
`diagonalMap_isRealizationEquivalence` is the equivalent existential form.

No compatible choice of rowwise inverses or inverse homotopies is assumed.
No groupoid, finite-dimensionality, or connectedness hypothesis is imposed.
This is an actual topological homotopy equivalence, not a formal comparison
or merely an unspecified group isomorphism.

## Proof modules

1. `MapEquivalence`: the property that a prescribed simplicial realization
   map is a homotopy equivalence; invariance under isomorphism squares,
   product with a locally compact realization, and genuine mono pushouts.
2. `BisimplicialLatching`: full and partial outer latching subcomplexes as
   unions of degeneracy images, and their canonical comparison maps.
3. `BisimplicialLatchingIntersections`: the inverse image of the preceding
   degeneracy union under the next degeneracy is exactly the corresponding
   lower-dimensional union. These give actual simplicial pushout squares.
4. `BisimplicialLatchingEquivalences`: finite induction on the degeneracy
   unions, using mono HEP and homotopy pushout gluing, proves latching-map
   realization equivalence from the row maps.
5. `BisimplicialSkeleton`: the generic outer filtration of the diagonal,
   its comparison maps, and its genuine exhaustive sequential colimit.
6. `BisimplicialSkeletonAttachment`: full-row enriched attachments
   `(L_n X × Δ[n]) ∪ (X_n × ∂Δ[n])`, their actual successor pushouts, and
   every canonical-map naturality square. Eilenberg–Zilber uniqueness is
   used to prove injectivity away from the attachment.
7. `BisimplicialEquivalence`: product/pushout gluing gives finite-stage
   equivalences; the established sequential mono-HEP theorem gives the
   final equivalence and identifies its forward map with the prescribed
   realized diagonal map.

The proof does not invoke a generic row-invariance result earlier in its
own dependency graph and introduces no new axiom or conclusion assumption.

## Verification and scope

All seven final source files compiled with pinned Lean 4.34.0, without
warnings or errors. The final endpoint has a matching `.olean`.
The complete frozen source manifest is
`logs/bisimplicial-realization-sources.sha256`.

`audits/BisimplicialRealizationAudit.lean` selects every declaration by its
origin among these seven modules, including private/generated declarations,
and recursively collects axioms. All 164 declarations passed. It permits only `propext`,
`Classical.choice`, and `Quot.sound`. Its full evidence is
`logs/bisimplicial-realization-audit.log`. All seven-source hash checks pass.
Checks run under the shared `/tmp/quillen-lean-slot-2.lock` with one Lean
process at a time.

This generic theorem is available to the developing Q/S comparison. It does
not itself prove the required degreewise Q/S row-groupoid equivalences or
the final algebraic K-theory comparison. It remains outside the earlier
immutable delivered archive pending the parent's independent source
rehash, endpoint-consumer checks, and integration.
