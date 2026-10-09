# Independent review: actual mapping-cylinder strict-fiber HELP

Accepted 2026-10-09 12:31:57 UTC.

## Frozen source

`Quillen/CategoryTheory/TheoremB/CompactMappingCylinderFibers.lean`.
Manifest: `logs/compact-mapping-cylinder-fibers-sources.sha256`.
The source was read completely. No production source or live artifact is changed.

## Exact semantic scope

The input is an actual mapping-cylinder pushout, obtained by attaching the
source cylinder at its terminal endpoint along the original map `f:A→C`,
and an arbitrary base map `C→T`. The resulting projection is literally the
original cylinder collapse followed by this base map.

The three strict-fiber maps are the original collapse, target inclusion,
and source inclusion. Each is defined by restricting the original continuous
map to the displayed strict subtypes, with the exact original base equation.
No identification of a strict fiber with a pushout is asserted or required.

The collapse on each fixed strict fiber is a genuine homotopy equivalence.
Its inverse is exactly the original target inclusion. The left inverse
homotopy is the actual target strong deformation retraction, restricted to
the strict fiber using its already proved base-preservation equation. The
other composite is strictly the identity by the original collapse/target
identity. The construction allows empty fibers and makes no HLP assumption.

The collapse composed with the original source inclusion is exactly the
original `HomotopyFiber.strictMapOver` for `f`. Full compact HELP of this
original fiber map therefore gives full compact HELP of the original source
inclusion, by genuine cancellation of the second HELP map. HELP for that
second map follows from the constructed homotopy equivalence. The underlying
cancellation theorem retains the complete supplied boundary homotopy on an
actual compact cylinder boundary; it does not replace the original forward
map with a selected inverse.

All topology APIs here have their explicit common-universe scope. No
separation, nonemptiness, CW-type, total-cylinder HLP or variable-base HELP
assumption or conclusion is inserted. The target deformation preserves the
base, but this is used only for restriction to each fixed strict fiber.
Actual collar transport and subsequent variable-base/global gluing remain
separate obligations.

## Independent verification

A first-path overlay excludes every target artifact family and rebuilds the
exact frozen source. One module-origin traversal recursively checks the
fixed **23** declarations against only `propext`, `Classical.choice` and
`Quot.sound`.

The **15 consumers** retain all nine authored tests, including the full
prescribed-boundary HELP signature, and add the exact strict retraction,
original attaching-map factorization at every point, the actual inverse
homotopy, original collapse homotopy-set maps in all finite degrees and
separately degree zero, and equivalence of emptiness of the strict fibers.

Audit: `audits/CompactMappingCylinderFibersIndependentAudit.lean`.
Replay: `logs/verify-compact-mapping-cylinder-fibers-independent.sh`.
Evidence directory: `logs/compact-mapping-cylinder-fibers-independent-20261009/`.

## Terminal evidence

The fresh source and fixed23/all15 audit passed warning-free. No implementation
or consumer repair was needed. The frozen source, **3,400 prerequisite sources**,
**15,734 dependency artifacts** and project/toolchain pins match before and after.
The rebuilt target is a regular fresh artifact, and actual first-path import
resolution is recorded. Every source file and live build artifact remains
unchanged. This acceptance is after the immutable 12:10 archive freeze.

- Source/import log: `logs/compact-mapping-cylinder-fibers-independent-20261009/check.log`
- Audit log: `logs/compact-mapping-cylinder-fibers-independent-20261009/audit.log`
- Terminal driver: `logs/compact-mapping-cylinder-fibers-independent-driver.log`
- Evidence manifest: `logs/compact-mapping-cylinder-fibers-independent-20261009/artifacts.sha256`
