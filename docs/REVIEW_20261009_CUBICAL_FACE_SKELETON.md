# Independent review: actual cubical faces and finite skeleta

## Scope and current status

This review covers exactly `Topology/CubicalSubdivision/{Walls,FaceComplex,
FaceBoundary,FaceIntersections}.lean`, frozen by
`logs/cubical-face-skeleton-sources.sha256`, fingerprint
`96f7aa34dac2e2c33ad64c95c6e577aa7a55fed94470f8f479a039b8d9fcb45e`.
**Accepted.** The complete semantic read, four fresh excluded-target source
rebuilds, and fixed-65 recursive-origin audit with all 28 exact consumers
passed warning-free at 11:11:26 UTC on 2026-10-09. Every source, dependency
and toolchain hash matched before and after. No audit or source correction
was needed for this independent run.

`StagePasting`, facewise lifting induction, and global gluing are outside
this review. The audit explicitly rejects `StagePasting` in its environment.
No production source is modified.

## Mathematical inspection

### Literal finite geometry

The cube remains the original product `Fin n → unitInterval`. Each coordinate
label specifies either an actual grid vertex `j/(m+1)` or a moving interval
`(k+t)/(m+1)`. Their finite bounds include both outer endpoints. Moving
coordinates form the actual finite subtype `Active F`; dimension is its
cardinality. The coordinate definition uses finite witnesses, but the fixed
and moving formulas prove that its values are the displayed original affine
ones, independent of witness choice.

Injectivity follows coordinatewise from the original interval maps.
Compactness of the finite product and Hausdorffness of the cube give genuine
closed embeddings. Face images are compact and closed. The r-skeleton is the
actual finite union of all face images of dimension at most r, hence compact
and closed; its top stage is the whole original cube by original cell
coverage. These assertions include dimension zero.

### Exact whole-boundary attaching geometry

Replacing an active coordinate by a grid vertex gives an actual new label.
Its active-coordinate embedding preserves the original indices and misses
the replaced coordinate, so its dimension is strictly smaller. When that
coordinate is at zero or one, the chosen vertex is exactly the corresponding
interval endpoint. The original point is unchanged in every coordinate.
Thus every point of the entire ordinary parameter-cube boundary lies in a
lower-dimensional face.

For the converse, an interior point of F forces every active coordinate of F
to be active in any face G containing that point: a moving interval meets a
grid vertex only at an endpoint. This gives an actual injection `Active F`
into `Active G`. If G has no larger dimension, finiteness makes that injection
surjective. The literal vertex-coordinate injection and the previously proved
interval intersection formulas then force equality of all face labels.
Therefore distinct equal-dimensional faces intersect only on both entire
parameter boundaries, and for dimension r+1 the preimage of the r-skeleton is
exactly the full original boundary. This is an equality of actual subsets,
not merely a statement about endpoint coverage.

At dimension zero the parameter boundary is empty. The same argument proves
that distinct vertex faces cannot intersect; no positive-dimension or
nonemptiness hypothesis has been silently introduced.

### Actual wall-map pasting

The walls are the images of the entire boundaries of all actual cells.
Original outer-boundary points belong to them, as shown directly from the
affine coordinate formulas. For a supplied continuous wall map and cell maps
matching it on their full boundaries, equal-cell intersections agree by
injectivity; distinct-cell intersections agree through their original
boundary values. The accepted finite quotient-pasting theorem then supplies
a continuous map on the original cube, preserving every cell map and the
entire supplied wall map. No separation property is required of the target.

For actual cell lifts, cell coverage proves that the pasted map is an actual
lift of the original whole-cube map. The wall map is genuine input data here;
its later construction is not claimed. There is no assumed HEP for an
arbitrary closed collar subset, no facewise existence-of-lifts conclusion,
and no local or global weak-cartesian gluing conclusion.

## Independent verification contract

The first-path overlay excludes every artifact family for all four targets,
as well as `StagePasting`. The four original source files are rebuilt into
fresh regular `.olean` files; dependency output checks that imports use them.
The accepted grid/pasting prerequisites were read, and their previous
independent review is `docs/REVIEW_20261009_CUBICAL_GRID.md`.

The frozen evidence includes hashes for all four sources, 2,973 recursively
resolved dependency sources, 13,806 dependency artifacts, and the project and
toolchain pins. These are checked before and after the run. The mutable public
umbrella is outside that frozen prerequisite closure; a combined
`Quillen.Library` import is nevertheless included in the actual consumer audit
to detect cross-branch declaration collisions.

The fixed-65 audit scans every declaration's actual defining origin,
including all private/generated declarations (Walls 9, FaceComplex 30,
FaceBoundary 12, FaceIntersections 14), and recursively permits only
`propext`, `Classical.choice` and `Quot.sound`.

Its 28 consumers include the author's 15 plus exact wall-map values,
genuinely empty zero-dimensional boundary and walls, zero-dimensional face
cardinality and all higher skeleta, closedness, unchanged fixed-face
coordinates, absence of boundaries and intersections for distinct vertex
faces, pointwise equivalence for the whole attaching preimage, exclusion of
all interior points from the preceding skeleton, and zero-dimensional
continuous pasting with no boundary constraint.

Audit: `audits/CubicalFaceSkeletonIndependentAudit.lean`.
Preparation: `logs/prepare-cubical-face-skeleton-independent.py`.
Replay: `logs/verify-cubical-face-skeleton-independent.sh`.
Evidence directory: `logs/cubical-face-skeleton-independent-20261009/`.

## Frozen source hashes

- Walls: `b8dc01ec87e99fc0979b269d30d087661400e829c46bb37df5ed6b77185d13a4`
- FaceComplex: `d612506531e37e38f3ccca6661ed607a6b0cfed427445271e184a7d0dbe9eb3c`
- FaceBoundary: `a8269f4a05ba8e2cfc8ea9c2b6f09065741174489111965835536071dedee40f`
- FaceIntersections: `5c6151e29349e1ef3389873614f505e76735fe8d36a98009a0f4ccd1902cd1e3`

Terminal driver: `logs/cubical-face-skeleton-independent-driver.log`.
Evidence manifest: `logs/cubical-face-skeleton-independent-20261009/artifacts.sha256`.
