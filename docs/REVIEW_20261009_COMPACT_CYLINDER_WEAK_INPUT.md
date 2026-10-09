# Independent review: finite cylinder lifting from weak original fibers

**Accepted, 2026-10-09 14:26:17 UTC.** All three fresh source builds,
the fixed defining-origin audit, twenty consumers, and before/after provenance
checks passed without warnings or errors. No production source or live artifact
was modified.

## Frozen sources

1. `Quillen/Topology/HomotopyFiber/ContractibleBaseWeak.lean`
2. `Quillen/Topology/HELP/WeakFiberCube.lean`
3. `Quillen/CategoryTheory/TheoremB/CompactMappingCylinderWeakBoundary.lean`

Manifest: `logs/compact-cylinder-weak-input-sources.sha256`, fingerprint
`fa606b4a9b4bc32ac3fa8bbfd2b4513fcd1fdd7ce6069469528435909aa6a495`.
All source text and the relevant exact-map prerequisites were inspected.
The weak-finite HELP4 and finite-cylinder9 prerequisites are independently
accepted, respectively at 14:20:31 and 14:24:14 UTC.

## Semantic assessment

`weak_of_strictFiber_contraction` uses the genuine strict-fiber inclusion
homotopy equivalences of both HLP projections over the supplied contracted
base. The actual fiber-map square is literal, so complete weak-equivalence
composition and cancellation prove weakness of the original total map.
The separate pullback lemma retains the original parameter and source map:
actual strict-pullback fiber homeomorphisms commute with the transition
exactly. No pullback stability of arbitrary weak equivalences is asserted.

For the original finite cube lifting problem, `weak_strictHELP_on_cube`
pulls both genuine fibrations back over the displayed target cube. Their
projections still have genuine HLP. The original fiber weak property at the
cube's distinguished base point and its explicit contraction make the actual
pulled-back transition weak. The accepted finite-cube HELP theorem gives a
relative filler, whose source coordinate supplies the original filler and
whole-boundary fixed comparison. This first lemma only requires that one
original fiber map to be weak.

`weak_strictHELP_on_cube_over_base` applies actual stationary correction,
using the cube boundary duration, to fix the original base exactly without
changing any boundary point. `weak_fullHELP_on_cube_over_base` first extends
the reverse supplied boundary homotopy over the fixed base by genuine HLP
and HEP. After the strict filler, a genuine vertical concatenation and the
accepted boundary-unpadding construction restore every value of the
original prescribed boundary path. The all-fiber weak hypothesis here is
explicit, since the intermediate target cube can change. The zero-cube uses
the same honest empty-boundary tests; no nonemptiness assumption is inserted.

For a displayed mapping cylinder, the original collapse followed by the base
map is the actual projection. The source-end proof first applies the preceding
finite theorem to the original attaching map, then lifts the resulting
relative comparison through the actual collapse. Compact HELP is used here
only for that collapse, which has a genuine homotopy equivalence. The source
projection retains its explicit compact locally compact HLP hypothesis; the
two original endpoint projections retain unrestricted HLP. The side-and-caps
correction keeps the exact source boundary, base, and full prescribed track.

The endpoint theorem packs these paths in the original vertical mapping-path
space and obtains literal finite cube-boundary RLP, including every stored
path coordinate. The realization-model wrapper derives the required compact
cylinder lifting property from a genuine homeomorphism of the original base
to a simplicial realization and the independently accepted finite-cylinder
construction. No full HLP of the mapping cylinder is inferred.

## Independent checks

The first-path overlay excludes every target artifact family and compiles all
three targets into fresh regular files. Actual `lean --deps` output confirms
these fresh artifacts are the imported targets. A single defining-module
traversal recursively audits fixed **10 = 2 + 4 + 4** origins, including
generated helpers, allowing only `propext`, `Classical.choice`, and `Quot.sound`.

The **20 consumers** retain all eleven final authored tests and add:

- the actual pullback fiber weak map, parameter/source coordinates and exact
  fiber-homeomorphism square;
- the strict finite vertical filler with its entire constant boundary;
- literal evaluation of the vertical endpoint at path time one;
- extraction of both the original boundary source and every stored path value
  from a general finite endpoint lift;
- complete weakness and all finite based homotopy-set bijections of the
  original source inclusion, by its actual constant-path section;
- full prescribed vertical HELP on the original zero-cube.

The existing tests also verify actual emptiness of the cylinder when its
source is empty, raw zero-dimensional endpoint lifting, unrestricted finite
dimensions, and the genuine realization-model wrapper. No desired lifting or
weak conclusion is inserted as a hypothesis of a consumer.

The dependency traversal starts from targets, the independent audit, and
implicit `Init`. All **3,664 prerequisite sources**, **16,546 dependency
artifacts**, target hashes, audit bytes, and toolchain/project pins were
verified before and after the run. No implementation or audit repair was
needed. The successful source/audit log has no warning, error, or `sorryAx`.

## Evidence and scope

- Independent audit: `audits/CompactCylinderWeakInputIndependentAudit.lean`.
- Preparation: `logs/prepare-compact-cylinder-weak-input-independent.py`.
- Replay: `logs/verify-compact-cylinder-weak-input-independent.sh`.
- Evidence directory: `logs/compact-cylinder-weak-input-independent-20261009/`.
- Terminal log: `logs/compact-cylinder-weak-input-independent-20261009/terminal.log`.
- Evidence manifest: `logs/compact-cylinder-weak-input-independent-20261009/artifacts.sha256`.

All spaces in this boundary share the explicit arbitrary universe `u`.
The weak-to-HELP conclusion is limited to actual finite cube-boundary pairs.
It does not provide arbitrary compact HELP, a chosen homotopy inverse, the
mixed open/closed gluing step, or the final Waldhausen fibration theorem.
This is post-freeze work outside the immutable 12:10 checkpoint.
