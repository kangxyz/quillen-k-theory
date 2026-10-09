# Independent review: local vertical endpoint lifting and original-map weakness

Accepted 2026-10-09 12:21:25 UTC.

## Frozen scope and reviewed prerequisites

- `Quillen/Topology/FiberwiseMappingPath/BoundaryLifting.lean`
- `Quillen/Topology/FiberwiseMappingPath/Locality.lean`
- `Quillen/Topology/FiberwiseMappingPath/LocalFiberHELP.lean`

Manifest: `logs/fiberwise-mapping-path-locality-sources.sha256`.
All three sources were read completely and remain untouched.

The model/restriction pair has its independent fresh2/fixed70 review in
`docs/REVIEW_20261009_FIBERWISE_MAPPING_PATH.md`. The full prescribed-boundary
over-base HELP prerequisite was independently accepted fresh3/fixed7/all9;
see `docs/REVIEW_20261009_FULL_HELP_OVER_BASE.md`. This review copies their
five accepted fresh artifacts into its own first-path overlay, hashes them,
and checks their unchanged bytes before and after the new builds and audit.

## Semantic assessment

### Packing genuine full HELP into strict endpoint lifting

Given an actual endpoint lifting square, the source boundary map supplies
its original source coordinate and every value of its stored vertical path.
The path is the supplied boundary homotopy, with its terminal value coming
from the original commutative square. The vertical condition follows from
the stored path condition, rather than from a chosen replacement path.

Full over-base HELP produces the source lift `c` and a homotopy `K` whose
entire boundary track equals the supplied one. Packing `K` into the original
vertical mapping-path space yields the lift. Its source and path coordinates
both agree on the boundary. Its endpoint is exactly the original target map.
The proof does not identify paths merely up to homotopy or at their endpoints.

The finite cube theorem derives the required HELP from actual HLP of both
original projections, the exact square `q ∘ f = p`, and full compact HELP of
every original strict-fiber map. It applies the separately proved full
contracted-test theorem using the actual cube contraction, its complete
boundary HEP and the actual continuous boundary duration. The duration's
zero locus is exactly that boundary. The zero-dimensional empty boundary is
included: its empty-product duration is one, and no boundary nonemptiness or
positive-dimensional assumption is introduced.

### Exact chart transfer and finite locality

A local lift is transferred by the actual restriction homeomorphism. Both
the prescribed whole boundary path and the endpoint map are retained.
Charts on the base become the actual inverse-image charts under `q` in `F`.
The accepted finite-face open-cover lifting theorem is applied to those
charts and the original endpoint map. No arbitrary inverse-image inclusion
is asserted to have HEP, and no continuous family of local inverse maps is
chosen.

The structural local criterion asks for genuine HLP of the restricted
source projection `q ∘ f` and restricted target projection `q`, and full
compact HELP of their literal restricted strict-fiber maps. These hypotheses
remain explicit. The restricted square is definitionally commutative, and
the map on each double-subtype fiber has exactly the original underlying
value `f x`.

### Exact complete weak conclusion

The endpoint's finite cube-boundary lifting yields its complete weak
homotopy-equivalence property by the accepted original cubical argument.
Composition with the genuine constant-path-section homotopy equivalence
yields the complete property of the original `f`, since
`endpoint ∘ inclusion = f` literally. No endpoint-preserving inverse is used.

The conclusion includes surjectivity onto actual path components and
bijectivity of the original `homotopyGroupMap` for every finite index type
`Fin n`, explicitly including `n = 0`. It covers empty spaces. There is no
Whitehead, CW-type, nonempty-source, connectivity or based-inverse premise.
The abstract restriction/open-cover theorems retain independent source,
target, base and cover universes. HLP/compact-HELP applications retain the
existing common-universe contract.

## Independent verification

The overlay excludes all artifact families of the three targets. The sources
are rebuilt in dependency order, with actual fresh import paths verified.
One declaration traversal recursively checks all target origins against only
`propext`, `Classical.choice`, and `Quot.sound`; the guard is **8 = 3 + 3 + 2**.

The **17 consumers** retain all seven authored signatures and add the literal
restricted square and double-subtype strict-fiber values, every original
finite homotopy map, degree zero separately, component surjectivity, the
empty-source consequence, strict endpoint surjectivity from the zero-cube,
an explicit original vertical path to every target point, and strict lifting
preserving the complete original boundary source/path coordinates.

Audit: `audits/VerticalMappingPathLocalityIndependentAudit.lean`.
Replay: `logs/verify-vertical-mapping-path-locality-independent.sh`.
Evidence directory: `logs/vertical-mapping-path-locality-independent-20261009/`.

## Scope remaining

This is a structural locality theorem for the displayed maps. It does not
supply the local HLP or strict-fiber HELP of the original bar/collar models.
Those concrete hypotheses and subsequent global Waldhausen fibration assembly
remain separate obligations. No later bar/collar source is in this review.

## Terminal result and evidence

All three source checks and the fixed8/all17 consumer audit passed warning-free.
No implementation or consumer repair was needed. The exact target source hashes,
**3,433 prerequisite-source hashes**, **15,784 dependency-artifact hashes**, the
five copied accepted prerequisite artifacts and project/toolchain pins agree
before and after. The new target oleans are regular fresh files, and actual
first-path import records confirm the rebuilt dependencies.

- Terminal driver: `logs/vertical-mapping-path-locality-independent-driver.log`
- Source/import log: `logs/vertical-mapping-path-locality-independent-20261009/check.log`
- Fixed audit log: `logs/vertical-mapping-path-locality-independent-20261009/audit.log`
- Evidence manifest: `logs/vertical-mapping-path-locality-independent-20261009/artifacts.sha256`
