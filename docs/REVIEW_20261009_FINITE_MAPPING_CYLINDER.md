# Independent review: finite mapping-cylinder lifting and full vertical HELP

Accepted 2026-10-09 14:24:14 UTC. No production source was changed by this review.

## Frozen scope

The nine sources listed in `logs/compact-mapping-cylinder-lifting-sources.sha256` were read semantically and rebuilt independently in order. The scope consists of the literal sum-subtype homeomorphism, compact parameter presentation, truncated times, actual piecewise lift, quotient descent, compact cylinder HLP, full-boundary vertical cancellation, contracted-test source HELP, and its exact finite cube-boundary endpoint.

The hypotheses remain substantive structural inputs: unrestricted Hurewicz lifting of the two original source/target projections; an explicitly closed matching locus, or a genuine realization homeomorphism giving compact closed graphs; and full compact HELP of each original strict attaching-fiber map for the source-end comparison. The cylinder conclusion is only compact locally compact parameter HLP. No weak-to-full-compact-HELP or weak-to-homotopy-equivalence conversion is used.

## Mathematical inspection

- The source piece lifts the original base homotopy until the cylinder reaches its glued cap. The shifted target lift then continues it. At the switching time and at an initially glued cap, the formulas agree literally for the entire time interval.
- Descent preserves the original parameter and point coordinates. Quotient preservation is invoked only after a locally compact product and restriction to the displayed closed matching locus. Arbitrary product or arbitrary pullback preservation is not assumed.
- The unrestricted original HLP is legitimately used on its possibly noncompact start-parameter spaces. The resulting restricted compact HLP is not substituted back into such a universal construction.
- Full vertical cancellation first lifts the actual side-and-both-caps boundary using genuine ordinary compact HELP. Duration correction fixes exactly that whole boundary, retains both endpoint maps, and restores the displayed base coordinate. The final prescribed track is the original track, not a replacement with the same endpoints.
- The cubical endpoint is the original fiberwise mapping-path endpoint. Dimension zero, empty tests, component coverage, and all stored boundary path values remain explicit.

This boundary does not prove the mixed open/closed attachment theorem, global weak-cartesian gluing, the two-sided-bar fiber theorem, or Waldhausen fibration.

## Independent validation

All nine target artifact families were excluded from a first-`LEAN_PATH` overlay. Each source was then freshly compiled there. The current held `Quillen/Library.lean` artifact family was also excluded and that actual public umbrella was freshly compiled afterward. Thus the combined-public consumer did not rely on an older umbrella olean.

The single-pass recursive origin audit fixed exactly 47 origins, with all nine modules present and per-module counts `[7, 9, 15, 2, 2, 2, 5, 2, 3]`. Only `propext`, `Classical.choice`, and `Quot.sound` occur. All 29 independent consumers passed warning-free, including the literal piece maps and cap seam, closed-locus quotient, full stored boundary paths, the original source-end weak map, explicit `Fin 0`, and empty-target consequences.

The closure contains 5,998 dependency sources and 26,969 dependency artifact files. It explicitly seeds the implicit core `Init.lean` and its artifact family recursively. Frozen source, dependency, toolchain/project-pin, and fresh-artifact hashes all match after validation.

The first precheck stopped before Lean because the live public umbrella had acquired new accepted imports. Its manifests and mismatch log are preserved under `initial-precheck/`. The successful replay used the subsequently held actual current umbrella; this was a harness refresh, not a mathematical source repair.

## Evidence

- Audit: `audits/CompactCylinderFiniteLiftingIndependentAudit.lean`
- Evidence directory: `logs/compact-cylinder-finite-lifting-independent-20261009/`
- Fresh compilation: `build-current-library.log`
- Fixed audit and consumers: `audit-initial.log`
- Frozen sources: `sources.sha256`
- Dependency closure: `dependency-sources.sha256`, `dependency-artifacts.sha256`
- Fresh target/public artifacts: `fresh-artifacts.sha256`
- Complete evidence index: `artifacts.sha256`
