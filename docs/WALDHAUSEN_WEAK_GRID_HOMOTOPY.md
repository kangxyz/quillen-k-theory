# Genuine weak-grid cylinder and exact-functor homotopies

## Frozen generic cylinder

The three modules in `logs/waldhausen-weak-grid-20261009/sources.sha256`
construct a genuine nerve-direction cylinder of actual two-degree Waldhausen
S-grids, and assemble compatible families into simplicial and realized
homotopies. Their underlying categories have arbitrary independent object and
hom universes. No preadditivity or exact-category structure is assumed.

`nerveCylinderDiagram η τ` evaluates the categorical natural-transformation
cylinder of `η : A ⟶ B` at the nerve time specified by `τ : [m] ⟶ [1]`.
On each S-row time is fixed, so all row maps and actual quotient pushouts are
unchanged maps and pushouts of one endpoint. A crossing nerve map is an actual
component of `η` followed by a weak map of `B`; closure under composition proves
weakness. Only pointwise weakness of the components is required.

The zero and one endpoints are strictly the original grid functors. Independent
interval and nerve reindexing commutes strictly with this cylinder.

`weakGridFamilyCylinder`, `diagonalWeakGridHomotopy`, and
`diagonalWeakGridRealizationHomotopy` apply to actual bisimplicial maps
`f, g : X ⟶ bisimplicialSSet W`. Their hypothesis is componentwise heterogeneous
equality of the actual transformation family after simultaneous reindexing.
Endpoint functor equalities follow from the given maps' ordinary naturality;
cylinder naturality and the resulting homotopy are proved, not assumed.
The simplicial endpoints are exactly `TheoremA.diagonalMap f` and
`TheoremA.diagonalMap g`, and realization retains these maps.

This frozen boundary does not assert basedness. Actual chosen-zero constancy
and exact-functor specializations are separate companion modules.

## Evidence

- Frozen manifest: `logs/waldhausen-weak-grid-20261009/sources.sha256`
- Manifest SHA-256: `d52f8bce057de00914a8ef46e34b616d3abd8edf2522cd92e04f27b3bf593f10`
- Focused successful naturality/assembly checks:
  `logs/waldhausen-nerve-cylinder-cont2.log`
- Recursive declaration-origin audit and exact consumers:
  `audits/WaldhausenWeakGridAudit.lean`
- Audit output: `logs/waldhausen-weak-grid-20261009/audit.log`

The audit enumerates every declaration whose defining origin is one of the
three modules, including private and generated declarations, and recursively
permits only `propext`, `Classical.choice`, and `Quot.sound`.

The standalone audit passed all **26** origins and fixes that expected count.
In the combined additivity audit, 25 declarations are attributed to these
three modules: the remaining generated declaration,
`SimplexCategory.const.eq_1`, is attributed there to the separately imported
`MixedOrdinalEndpoints` module. The exact name-set comparison is recorded in
`logs/waldhausen-weak-grid-20261009/origin-count-comparison.log`; no declaration
is lost from the combined audit and all other helper names agree exactly.
