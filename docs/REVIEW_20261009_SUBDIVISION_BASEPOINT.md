# Independent review: actual based forward subdivision isomorphism

Accepted 2026-10-09 06:24 UTC after full semantic inspection, fresh isolated
rebuild, fixed-count recursive axiom audit, exact-map consumers, and source
and inspected-dependency rehashes.

## Accepted scope

`Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean` defines the original
constant-zero grid in outer degree delta[0] and inner degree [0], and its actual
realization point. Restricting by the original first-half endpoint takes this
grid literally to the original diagonal zero vertex. Realization naturality
therefore proves actual forward basepoint preservation without choosing a path.

The reviewed ordinary outer-subdivision homotopy equivalence has precisely
this original endpoint as its forward map. Applying the previously established
`homotopyEquivPiEquiv` gives an isomorphism in every positive homotopy degree,
including the possibly nonabelian fundamental group. Its forward homomorphism
is exactly `piMap` of that original endpoint; surjectivity follows directly.
Neither the inverse nor the inverse homotopies are assumed based. The statement
does not claim a zeroth homotopy-group result or based additivity by itself.

No mathematical or implementation defect was found.

## Independent checks

The source was rebuilt into an isolated artifact overlay excluding its live
source-origin artifacts. The audit's `--deps` output resolves the fresh actual
olean. Both rebuild and final audit are warning-free. The frozen source and
inspected previously accepted dependencies match their pre-check hashes.

`audits/SubdivisionBasepointIndependentAudit.lean` recursively audits exactly
10 declaration origins, including private/generated declarations, allowing
only `propext`, `Classical.choice`, and `Quot.sound`. It tests independent object
and hom universes, actual grid/point equalities, the exact forward homomorphism,
its injectivity and surjectivity, and cancellation of actual based forward
precomposition for monoid homomorphisms into an arbitrary monoid. The latter
consumer uses surjectivity alone and takes no based inverse as input.

## Evidence

- Frozen manifest: `logs/additivity-subdivision-basepoint-sources.sha256`
- Independent build/audit/import-resolution/hash evidence:
  `logs/subdivision-basepoint-independent-20261009/`
- Independent audit: `audits/SubdivisionBasepointIndependentAudit.lean`

This review does not modify the frozen source or its live build artifacts.
