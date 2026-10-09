# Independent review of the actual cubical grid boundary

## Scope and status

The reviewed sources are exactly `Topology/CubicalSubdivision/{Grid,Cover,
Faces,Pasting}.lean`, frozen by `logs/cubical-grid-sources.sha256`, manifest
SHA-256 `37154681a92a4b2c9f4fc7ecae306217bc7281fa364b083b4c132f07d14200e8`.
**Accepted.** The complete semantic inspection, four fresh source rebuilds,
fixed46 recursive-origin audit and all31 strengthened consumers passed
warning-free. All source/dependency/toolchain hashes match before and after.
Only a driver-level `Fin (0+1)` inference needed the explicit arithmetic
proof described below; the frozen production sources were unchanged.

`Walls` and `FaceComplex` are outside this review. The independent audit
explicitly rejects either module appearing in its imported environment.

## Mathematical review

- **Actual cells and coverage.** The cube is literally `Fin n → unitInterval`.
  Each coordinate is exactly `(k+t)/(m+1)`, with a positive denominator.
  Interior coverage uses the natural-number floor of `(m+1)x`, and the
  outer endpoint `x=1` is treated separately by the last cell at parameter1.
  Product coverage chooses these original coordinate preimages.
- **Finite closed cover and mesh.** The index set is genuinely finite.
  Compactness of the original cube gives compact cell images; Hausdorffness
  makes them closed. The distance bound is proved first on the interval
  and then in the actual finite-product sup metric. Diameter is bounded
  by `1/(m+1)`. No argument requires a positive cube dimension.
- **Uniform whole-cell subordination.** The compact metric Lebesgue-number
  theorem is applied to the genuine open cover of the cube. A single grid
  mesh is chosen uniformly, and each entire nonempty closed cell lies in
  one chosen open set. Pullback along a genuine continuous map retains
  arbitrary target topology. The two literal height collars use the
  overlapping inequalities `h<3/4` and `1/4<h`; the conclusion concerns all
  points of each cell, rather than its vertices alone.
- **Faces and intersections.** Affine coordinate injectivity gives actual
  closed embeddings. Ordered intersecting interval cells must be adjacent,
  with preimages exactly1 and0. Distinct product cells therefore force an
  actual coordinate endpoint in each preimage, so both belong to the full
  original cube boundary. The shared-face equality retains the literal
  coordinate updates. This is not a claim that all finite face attachments
  or relative lifting properties have been constructed.
- **Quotient and pasting.** The finite disjoint union of the compact cells
  is compact. Its continuous original affine projection is surjective
  onto the Hausdorff cube and hence is a quotient map. Compatible
  continuous cell maps descend continuously into an arbitrary target;
  no target separation assumption is introduced. Coverage proves
  uniqueness, and any already specified subset is retained pointwise.
  No HEP assertion about that subset is used.

These statements supply concrete geometry and continuous pasting of
already-given compatible maps. They do not prove existence of compatible
face lifts, finite weak-cartesian gluing, or the global diagonal fiber theorem.

## Independent checks

All target artifact families were excluded from the first-path overlay.
The four source files were rebuilt into fresh regular files, and import
resolution must show the fresh targets. The exact frozen source hashes,
2,970 recursively resolved dependency sources, 13,803 dependency artifacts,
and the project/toolchain pins are checked before and after. The dependency
closure excludes mutable public umbrellas and the unreviewed face drafts.

The single-traversal audit requires all four origins and exactly46
declarations: Grid26, Cover6, Faces6, Pasting8. It recursively permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The 31 consumers include the original18 plus literal outer endpoint
formulas, the unsubdivided-cell identity, finite-index/sigma compactness,
zero-dimensional cell identity/full coverage/quotient/pasting, direct
injectivity, the same-cell-or-full-boundary dichotomy, whole-image height
collars, and boundary-compatible pasting into an arbitrary topological target.
The extra degree-zero arithmetic uses an explicit `Fin.ext` proof, avoiding
a reducibility-sensitive `Subsingleton (Fin (0+1))` synthesis request.

- Audit: `audits/CubicalGridIndependentAudit.lean`
- Full replay: `logs/verify-cubical-grid-independent-r1.sh`
- Terminal audit replay: `logs/resume-cubical-grid-independent-audit.sh`
- Evidence: `logs/cubical-grid-independent-20261009-r1/`
- Terminal driver: `logs/cubical-grid-independent-terminal-driver.log`

No production source or live build artifact is modified by this review.

Terminal evidence manifest: `logs/cubical-grid-independent-20261009-r1/artifacts.sha256`.
