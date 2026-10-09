# Partial edgewise subdivision on a bisimplicial diagonal

The new standalone module `Quillen.Topology.Realization.EdgewiseBisimplicial`
proves actual homotopy equivalences for subdivision in either bisimplicial
direction, with the realized partial endpoint as the exact forward map.
It is separate from the earlier frozen five-file edgewise endpoint scope.

The Q/S-facing endpoint is:

```
Quillen.Edgewise.upperIndexRealizationHomotopyEquiv
  (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
  ContinuousMap.HomotopyEquiv
    |TheoremA.diagonalSSet (Edgewise.ε.op ⋙ X ⋙ Edgewise.subdivisionFunctor)|
    |TheoremA.diagonalSSet (Edgewise.ε.op ⋙ X)|
```

Its `toFun` is definitionally the realization of
`TheoremA.diagonalMap (Functor.whiskerLeft (Edgewise.ε.op ⋙ X) Edgewise.endpointNatTrans)`.

## Proof

Horizontal and vertical endpoint restrictions commute. Double subdivision
on the diagonal identifies with ordinary edgewise subdivision of that
diagonal. In a chain of three alternating partial restrictions, both
adjacent composites are therefore the already-proven edgewise realization
equivalence. The explicit `HomotopyFiber.ofAdjacentComposites` construction
proves the outer partial restriction itself is an equivalence, retaining
its prescribed forward map. No generic rowwise-invariance theorem is used
or assumed.

## Verification

The full source compiled with Lean 4.34.0 without warnings or errors.
`audits/EdgewiseBisimplicialAudit.lean` independently audited all 21 origin
module declarations, including private/generated ones, allowing only
`propext`, `Classical.choice`, and `Quot.sound`. Transitive axioms for all
three realization equivalences were printed explicitly.

Source hash: `logs/edgewise-bisimplicial-sources.sha256`.
Build/audit logs: `logs/edgewise-bisimplicial.log` and
`logs/edgewise-bisimplicial-audit.log`.

This proves the partial subdivision bridge only. It does not assert that
an arbitrary rowwise equivalence induces a diagonal equivalence; that
separate gluing theorem remains under development.
