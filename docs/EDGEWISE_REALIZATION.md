# Edgewise realization endpoint

## Proven result

`Quillen.Edgewise.realizationHomotopyEquiv X` is an actual topological homotopy
equivalence `|subdivision X| ≃ₕ |X|` for every simplicial set, including
infinite-dimensional simplicial sets. No finiteness, connectedness, or
contractibility hypotheses are imposed on X.

The forward continuous map is definitionally the realization of the canonical
second-half simplicial endpoint. `realizationHomotopyEquiv_toFun` records this
identity. `realizationHomotopyEquiv_naturality` proves commutation with every
simplicial map. `realizationHomotopyEquiv_point` records the map on arbitrary
subdivided vertices, and `realizationHomotopyEquiv_vertex` preserves a chosen
original vertex represented by its degenerate interval.

The chosen inverse is not claimed to be canonical or simplicially induced.
The endpoint map is a homotopy equivalence; it is not claimed to be a
homeomorphism.

## Proof route

1. Edgewise uses the actual ordinal functor `[n] ↦ [n]ᵒᵖ ⋆ [n]`.
2. EdgewiseSimplex gives an explicit simplicial cylinder contracting each
   subdivided standard simplex to the interval `(0,n)`, checks both endpoints,
   and realizes that cylinder to a genuine continuous contraction.
3. Standard simplices are contractible via their actual nerve model.
4. EdgewiseCellular glues the specified comparison over genuine skeletal
   pushouts using monomorphism realization HEP, then over their sequential
   colimit using the proved sequential homotopy invariance theorem.
5. EdgewiseRealization supplies all colimit/monomorphism preservation instances
   and applies that cellular criterion without assuming the desired result.

## Frozen sources and verification

The five-source manifest is `logs/edgewise-realization-sources.sha256`:
MonomorphismHEP, Edgewise, EdgewiseCellular, EdgewiseSimplex, EdgewiseRealization.

The final EdgewiseSimplex and EdgewiseRealization sources were checked directly
with Lean 4.34.0, and their `.olean` files were generated. The final checks of
those two modules produced no warnings or errors. Commands used:

```
lake env lean -o .lake/build/lib/lean/Quillen/Topology/Realization/EdgewiseSimplex.olean Quillen/Topology/Realization/EdgewiseSimplex.lean
lake env lean -o .lake/build/lib/lean/Quillen/Topology/Realization/EdgewiseRealization.olean Quillen/Topology/Realization/EdgewiseRealization.lean
lake env lean audits/EdgewiseRealizationAudit.lean
```

All checks ran under `flock /tmp/quillen-lean-slot-2.lock`. Logs:
`logs/edgewise-simplex.log`, `logs/edgewise-realization.log`, and
`logs/edgewise-realization-audit.log`.

The focused audit passed all 108 declarations in the frozen five-module scope.
It selects every declaration by origin module, including
private/generated declarations, recursively collects its axioms, and permits
only `propext`, `Classical.choice`, and `Quot.sound`. It also prints transitive
axioms for the main endpoint and its naturality/basepoint laws.

This completes the edgewise realization theorem. It does not establish the
separate Waldhausen S-to-Quillen Q comparison equivalence. The parent is
independently rechecking the frozen scope before public integration.
