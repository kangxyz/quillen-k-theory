# Independent review: finite-parameter quotient descent

**Accepted, 2026-10-09 13:18:51 UTC.** Fresh excluded-target builds and the final fixed-origin/consumer audit passed warning-free.

## Frozen scope

- `Quillen/Topology/Maps/CompactParameterQuotient.lean`
- `Quillen/Topology/Realization/CompactGraph.lean`
- `Quillen/Topology/Pushout/CompactParameter.lean`

Manifest: `logs/compact-parameter-quotient-sources.sha256`.
All three sources were read completely. No production source or live artifact
is modified. SumSubtype, cylinder-parameter lift and Times drafts are outside
this boundary, which is after the immutable 12:10 archive freeze.

## Semantic assessment

A quotient restricted over a closed target subset remains quotient. The proof
uses the actual subtype topologies, the closed embeddings of that subset and
its preimage, and the original quotient's closed-preimage characterization.
Surjectivity is inherited by the actual restricted map. Closedness is explicit;
no arbitrary-subset restriction rule is assumed.

For a locally compact parameter `D`, the literal product `(x,d) ↦ (q x,d)`
is quotient. The proof equips the same target set with the coinduced topology,
uses the established continuous product-descent theorem to prove the identity
map continuous from the original product topology, and proves both topology
inequalities. Surjectivity retains the original parameter coordinate. There
is no arbitrary-product preservation assertion or hidden separation premise.

Combining these results gives the actual matching-subspace quotient over an
explicitly closed locus `p(y)=b(d)`. That version does not even require a
topology on the set of matching labels. A closed graph of the supplied test
map is a separate sufficient condition, proved by a continuous preimage and
symmetry of equality. A Hausdorff base is another explicit sufficient condition,
not silently assumed in the more general statements. The source, quotient,
parameter and label/base universes remain independent.

For an actual simplicial realization, a compact-source map factors through a
finite realized subcomplex. Its realization is Hausdorff and its original
inclusion is a closed embedding. The graph is closed in the product with that
finite subcomplex, and the product closed embedding sends it to exactly the
original graph in the unchanged realization. Both directions of this image
identity use the actual factorization equation. This proves closedness without
assuming the whole realization Hausdorff, replacing its topology, or requiring
the compact parameter to be Hausdorff. Local compactness is additionally
required only where quotient product descent is invoked.

For an actual TopCat pushout, the sum of its original legs is quotient.
Surjectivity follows from the actual pushout representatives; the closed-set
criterion follows from the genuine colimit topology and the two leg preimages.
Pulling this literal quotient back over a closed matching locus, or a compact
locally compact realization-valued test, preserves its quotient topology by
the preceding proved results. The output is the original coordinate map from
the sum-of-legs matching subspace, not a substituted quotient presentation.

## Independent checks

The first-path overlay excludes all target artifact families and rebuilds the
three sources in order. A single module-origin traversal recursively checks
fixed **11 = 5 + 3 + 3**, accepting only `propext`, `Classical.choice` and
`Quot.sound`. Narrow target imports avoid mutable public umbrella artifacts;
the author's separately recorded audit includes the public umbrella.

The **20 consumers** retain all thirteen authored original-map/universe/empty/
point tests. Added tests preserve an uninterpreted matching-label type, empty
closed restriction, actual continuous-descent formulas for the product,
matching pullback and original pushout-leg quotient, and actual finite cubes
including dimension zero. No quotient conclusion is assumed as its own input.

All **3,378 prerequisite sources** and **15,852 dependency artifacts**, the toolchain/project pins, and the three frozen target hashes were checked before and after verification. The fresh target artifacts were regular files and their actual import paths were confirmed. Their hashes were pinned across the final audit replay. All production sources and live artifacts remained unchanged.

The initial independent audit passed all eleven origins, but four added consumers hit a parsing conflict between simplicial bar notation and set-builder syntax. Those audit-only statements were rewritten using `Set.ofPred`; the original diagnostic log is retained. The final replay passed all twenty consumers without warnings or errors.

Audit: `audits/CompactParameterQuotientIndependentAudit.lean`.
Fresh-build replay: `logs/verify-compact-parameter-quotient-independent.sh`.
Final audit replay: `logs/finalize-compact-parameter-quotient-independent.sh`.
Final log: `logs/compact-parameter-quotient-independent-20261009/audit-fixed11.log`.
Evidence directory: `logs/compact-parameter-quotient-independent-20261009/`.

## Remaining scope

This is a genuine quotient-topology result for the displayed finite-parameter
matching construction. It does not assert arbitrary pullback preservation,
pullback stability of cofibrations, compact/Hurewicz lifting, weak-equivalence
base-change stability, or global Waldhausen fibration gluing. The later lift
construction must separately use these exact quotient maps and prove its
boundary and base equations.
