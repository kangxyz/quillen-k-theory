# Actual finite cubical face skeleta

## Frozen source boundary

The four companions `CubicalSubdivision/Walls`, `FaceComplex`, `FaceBoundary`,
and `FaceIntersections` are frozen by
`logs/cubical-face-skeleton-sources.sha256` (fingerprint
`96f7aa34dac2e2c33ad64c95c6e577aa7a55fed94470f8f479a039b8d9fcb45e`).
All four final sources compile warning-free. The initial exhaustive
recursive-origin audit passed 65 declarations and 15 consumers, using only
the standard three axioms. The final fixed-65 rerun and all 15 consumers
also passed warning-free, with frozen source hashes unchanged. Evidence is
indexed by `logs/cubical-face-skeleton-evidence.sha256`.
`StagePasting` and later lifting arguments are outside this source boundary.

## Canonical faces and the original topology

A face labels each coordinate either by an actual grid vertex or by an
actual moving grid interval. Shared geometric faces therefore have canonical
labels. The parameter space is the ordinary product of unit intervals indexed
by the actual finite set of moving coordinates, with no quotient or modified
topology. The coordinate map, closed embedding, and its fixed/moving formulas
are proved. The face dimension is the cardinality of those coordinates.

The r-skeleton is the finite union of images of faces of dimension at most r.
It is compact and closed in the original cube; the final skeleton is the
whole cube, including dimension zero.

## Genuine attaching geometry

Fixing one moving coordinate at either endpoint gives a labeled face of
strictly smaller dimension. Its parameter map preserves all remaining
coordinates. Thus the entire original boundary of each new face lands in
the preceding skeleton.

Conversely, an interior point forces every moving coordinate to remain moving
in any other face containing that point. This gives an actual injection of
the finite coordinate sets. If the second face has no larger dimension,
cardinality forces surjectivity; the literal integer-grid coordinates then
force equality of both face labels. Consequently:

- distinct equal-dimensional faces intersect only on both original boundaries;
- a face of dimension r+1 has preimage of the r-skeleton exactly equal to its
  whole original cube boundary.

No HEP of an arbitrary inverse-image collar subset is assumed.

## Grid walls and exact pasting

The actual grid walls are images of all whole cell boundaries. The original
outer cube boundary is contained in those walls. Continuous cell fillers
agreeing with a supplied continuous wall map paste by the proved finite
quotient presentation of the original cube. The result retains every cell
map and the entire original wall map. If those cell maps are actual lifts,
the pasted map is an actual lift of the original whole-cube map.

This result explicitly requires the wall data. It does not hide the later
lower-dimensional construction of that data in its hypotheses.

## Remaining proof work

The concrete finite-stage continuous extension, the relative face-skeleton
lifting induction, and weak double-cylinder/cartesian gluing are later layers.
The global connected-row diagonal fiber theorem is still open.
