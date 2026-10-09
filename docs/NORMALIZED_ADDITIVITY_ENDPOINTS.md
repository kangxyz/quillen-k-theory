# Genuine normalized additivity endpoint families and fixed-zero homotopies

## Scope

The two sources in
`logs/normalized-endpoint-families-20261009/endpoint-sources.sha256`
construct the actual endpoint isomorphism families after chosen-zero
normalization, prove independent interval/nerve reindexing coherence, and
package genuine simplicial and realized homotopies with strictly constant
zero tracks. They are valid for arbitrary independent object and hom universes,
with source and target categories sharing the object/hom universe pair required
by the existing S-set map API.

The inputs are genuine Waldhausen structures, structurally exact functors,
and the actual pointwise/relative cofibration transformation. The separated
endpoint additionally uses a genuine structural cofibration sequence and
binary coproducts in the target. There is no additivity/K-equivalence or
fixed-track hypothesis.

## Actual endpoint families

`normalizedIdentityEndpointIso` is the composite

1. inverse of the actual pushout normalization isomorphism, whiskered by the
   identity-interval arrow diagram;
2. the already proved actual identity endpoint isomorphism;
3. the canonical `Quillen.rebaseFunctorIso` of the original middle functor.

Its target is exactly the original `bisimplicialSSetMap` for `hG.rebase`.
Thus it matches the canonical normalization used by the public Waldhausen
K-map API, rather than a newly chosen endpoint map.

`normalizedSeparatedEndpointIso` analogously composes the inverse pushout
normalization, the actual cofiber endpoint isomorphism, and the actual
normalization isomorphism of the common pair-sum functor. Its target is exactly
`normalizedSumMap V W hs.exactH hs.exactF`.

The associated `...EndpointFamily` components are actual natural-isomorphism
components, so their weakness is proved using the Waldhausen isomorphism axiom.
The two `...EndpointFamily_reindex_app` theorems prove componentwise HEq for
independent interval and nerve restrictions. The identity case uses the frozen
identity family coherence and the actual conjugating components. The separated
case uses equality of the actual reindexed input arrow; the cofiber witness
proofs are propositions, so the entire conjugated comparison is unchanged.
Neither cylinder naturality nor a desired homotopy is taken as an input.

## Exact homotopies and fixed points

`NormalizedEndpointHomotopies.lean` applies the genuine weak-grid cylinder to
these proved families. The resulting simplicial and realized homotopies retain
exactly the normalized identity/separated maps and their canonical middle/common
sum targets.

The `...Homotopy_fixed_zero` theorems prove equality of the complete simplicial
vertex track with the constant chosen-zero track. Both endpoint diagrams have
literal object values `W.zero` on constant-zero input diagrams: this follows
from the actual normalized interval/sum functors and canonical rebase formula.
The generic zero-cylinder theorem then supplies map equality by zero uniqueness.
No identity component or basedness condition is assumed.

The `...RealizationHomotopy_fixed_zero` theorems lift those strict simplicial
track equalities to every `t : unitInterval`. The identity source point is
`realizationPoint (diagonalZeroVertex V)`; the separated source is the actual
`subdivisionBasepoint V` from `Additivity.SubdivisionBasepoint`. Both target
points are `realizationPoint (diagonalZeroVertex W)`.

## Boundary

These are the two endpoint homotopies and their actual fixed-zero proofs.
The mixed deformation homotopy, based subdivision cancellation, final based
additivity assembly, and equalities of K-group homomorphisms are separate
modules. No new global cylinder, fibration, or Gillet–Waldhausen theorem is
asserted here.

## Verification evidence

- Frozen source manifest:
  `logs/normalized-endpoint-families-20261009/endpoint-sources.sha256`
- Manifest SHA-256:
  `999ccf5869f3a178766ddac3622469cdbba5e07d14eb635268839c47010e5ddd`
- `NormalizedEndpointFamilies.lean` SHA-256:
  `6f26b89e3911efbff9b8a98e4fbea164218a6784c80d6c5d1fb5d1542d035953`
- `NormalizedEndpointHomotopies.lean` SHA-256:
  `e95fe6bb127ed04ad15bbf9b5b713202795a51bec3c1ea5ac2f0cc5fceee3696`
- Warning-free source checks:
  `logs/additivity-NormalizedEndpointFamilies.log`,
  `logs/additivity-NormalizedEndpointHomotopies2.log`
- Family-only audit: `audits/NormalizedEndpointFamiliesAudit.lean`
- Combined audit: `audits/NormalizedEndpointAudit.lean`
- Audit logs: `logs/normalized-endpoint-families-20261009/`

The family-only audit passed all17 origins. Audits enumerate all defining-origin
constants, including private/generated declarations, and recursively allow only
`propext`, `Classical.choice`, and `Quot.sound`. Exact consumers check the actual
conjugated component formulas by `rfl`, the precise original normalized target
maps, arbitrary independent universe levels, and the actual fixed zero points.

The combined fixed30-origin rerun passed with all strengthened consumers,
including explicit zero/one simplicial endpoint map equalities and both
realized fixed-point formulas. Both frozen source hashes matched afterward.
Final output: `logs/normalized-endpoint-families-20261009/final-audit.log`.
