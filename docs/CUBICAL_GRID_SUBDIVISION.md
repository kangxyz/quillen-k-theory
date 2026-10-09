# Explicit compact cubical grids for collar tests

The core four-source layer is `Topology/CubicalSubdivision/{Grid,Cover,Faces,Pasting}`.
Its final fixed-count validation and independent review status are recorded in
the associated audit evidence. Later wall and finite face-skeleton companions
are outside this core boundary until separately checked.

## Actual geometry

`Cube n` is literally `Fin n → unitInterval`, with its original product
topology and metric. For a grid parameter `m`, cells are indexed by
`Fin n → Fin (m+1)`, and their original coordinate formula is
`(k(i)+t(i))/(m+1)`.

The proof gives actual coverage (including outer endpoint 1), compact and
closed cell images, injectivity and closed embeddings, and the uniform mesh
bound `diam(cell) ≤ 1/(m+1)`. No positive-dimension premise occurs. Adjacent
cells agree on their literal common face. Equality between two distinct cell
parametrizations forces both preimages into the entire original cube boundary;
the stronger formula identifies an adjacent coordinate and its exact endpoint
values.

## A uniform finite collar choice

Compactness and the metric Lebesgue-number lemma select one grid for any
open cover pulled back along a genuine continuous cube map. Every point of
each closed cell lands in its selected open set. In particular, the actual
height collars `h<3/4` and `1/4<h` have a single uniform subordinate grid.
This is a statement about the whole cell, not just its vertices.

## Continuous finite pasting

The disjoint union of the finite compact cells maps by their original affine
maps onto the Hausdorff cube. It is an actual quotient map. Compatible
continuous cell maps therefore descend continuously into any target space;
no separation hypothesis on the target is used. The pasted map agrees with
every prescribed cell map, is unique, and retains any already specified
subset pointwise.

## Purpose and remaining boundary

These are concrete inputs for compact-parameter collar arguments. They do
not assert that arbitrary closed inverse images of collars have HEP. Later
lifting must proceed through actual cubical faces, with compatibility on
shared boundaries.

The finite face-skeleton lifting induction, local weak/cartesian gluing,
and the connected-row global diagonal fiber theorem remain separate proof
obligations. This layer neither assumes nor concludes those statements.

## Author validation boundary

The core four sources are frozen by `logs/cubical-grid-sources.sha256`
(fingerprint `37154681a92a4b2c9f4fc7ecae306217bc7281fa364b083b4c132f07d14200e8`).
All final sources compile warning-free. The single-traversal recursive-origin
check `audits/CubicalGridAudit.lean` fixes 46 defining-module declarations and
checks 18 consumers, including explicit zero-dimensional mesh/coverage and
independent target/index universes. The final run is warning-free and accepts
only `propext`, `Classical.choice`, and `Quot.sound`; source hashes match.
Evidence is indexed by `logs/cubical-grid-evidence.sha256`.
