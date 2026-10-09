# Exact local vertical endpoint lifting

Frozen sources: `logs/fiberwise-mapping-path-locality-sources.sha256`.
The three modules are `FiberwiseMappingPath/BoundaryLifting`, `Locality` and
`LocalFiberHELP`. They depend on the separate actual model/restriction pair
and the separately reviewed full over-base HELP boundary.

## Canonical maps and structural hypotheses

For `f : E → F` over `q : F → B`, the endpoint of `Space q f` stores actual
paths entirely within one fiber of `q`. `endpoint_hasLiftingProperty_of_pairHELP`
turns full vertical prescribed-boundary HELP into strict lifting of that
endpoint. Equality on the boundary includes every stored path value.

`endpoint_boundaryLifting_of_fiberHELP` supplies that HELP from actual HLP
projections `p,q`, the exact square `q ∘ f = p`, and full compact HELP of every
original strict-fiber map. The actual lifted finite cube and its entire boundary
provide the contracted test, including degree zero.

`endpoint_boundaryLifting_of_open_cover` uses the exact restriction
homeomorphism and the proved finite-face gluing theorem. It assumes actual
boundary lifting of the vertical endpoint on each base chart, rather than
identifying local and global ordinary mapping paths.

The final structural endpoint is
`isWeakHomotopyEquivalence_of_local_fiberHELP`. It assumes an actual open cover
of `B`; HLP of both displayed restricted projections; and full HELP of their
literal restricted strict-fiber maps. It concludes the complete empty-aware
weak property of the original `f`, including all finite based dimensions.
The final composition is literally `endpoint ∘ constantPath = f`, using the
proved scaling homotopy equivalence. No based inverse, component nonemptiness,
continuous inverse family or Whitehead assertion is inserted.

The model, restriction and abstract local-lifting part permit independent
source, target and base universes. The HLP/HELP structural application uses
the established common-universe convention of those test properties.

## Validation

All three frozen sources compiled warning-free. The author single-pass audit
recursively scans all eight actual defining origins and checks all seven
endpoint signatures. Only the standard three axioms occur.

- Audit: `audits/VerticalMappingPathLocalityAudit.lean`
- Initial full scan and consumers: `logs/fiberwise-mapping-path-locality-audit-initial.log`
- Source checks: `logs/fiberwise-mapping-path-{lifting,locality,local-help}-check1.log`

## Remaining global obligation

This does not yet establish the original two-sided-bar projection's local
HLP or the normalized global comparison's chartwise strict-fiber HELP.
Global mapping-path base paths can leave a chart. The exact finite
weak-cartesian collar/gluing identification remains a separate theorem;
these structural hypotheses must be derived from the original row maps,
not inferred from the desired global fiber conclusion.
