# Independent review: weak coproduct assembly

## Accepted scope

Accepted after full semantic review, fresh isolated compilation of both
sources, and a warning-free fixed-six recursive-origin audit with 17 exact
consumers. The terminal audit completed at 09:48:31 UTC on 2026-10-09.
Original source and inspected prerequisite hashes were rechecked unchanged.
The frozen source manifest is `logs/weak-coproduct-sources.sha256`; its
independent copy has fingerprint
`88e855a2f3507061af4d1c174622e208eaa232b567a1f884982b39a214334d41`.

- `Topology/HomotopyFiber/WeakCoproduct.lean`:
  `fa947b47a901d65e0cbac963bba4be3c7631cfc4da006567a748272e5a5a0921`
- `Topology/HomotopyPullback/WeakCoproduct.lean`:
  `8bbf1681db3ad439774abd96be89a739cffe11985e5b0614b08f8c5f0504f205`

Paths above are relative to `Quillen/`. The original sources are unchanged.

## Mathematical and original-map check

`WeakCoproduct.fiberHomeomorph` is an actual homeomorphism from the fiber
of a summand map at `y` to the fiber of the original index-preserving sigma
map at `⟨i,y⟩`. The source becomes `⟨i,x⟩` and the entire compact-open path
is postcomposed with `ContinuousMap.sigmaMk i`; both formulas are
definitional. The supporting component-pullback homeomorphism was read:
its forward map is inducing and injective, and surjectivity follows because
an actual path in a topological coproduct lifts into one summand. Endpoint
conditions select that same summand. There is no discreteness assumption
on a summand and no assumed inverse to the desired weak equivalence.

The original sigma map is weak by the accepted actual-fiber criterion.
Nonempty fibers are transported through the homeomorphism. Bijectivity of
the actual finite homotopy-set maps of a genuine homeomorphism transfers
subsingleton fiber homotopy sets. This uses all degrees, including zero;
component surjectivity is retained separately, so empty sources or indices
are handled correctly.

The fixed-target canonical comparison factors definitionally through the
sigma of the original component comparisons and the actual
`sigmaPullbackHomeomorph`. Its original parameter, source and constant path
are retained. Weak coproduct closure and this genuine homeomorphism prove
the displayed canonical comparison weak without a hidden cartesian
conclusion among the hypotheses.

## Exact scope

One arbitrary common universe contains the index type and all spaces.
There are no compactness, separation, connectedness, local-contractibility,
fibration or nonemptiness assumptions. Each component map/comparison must
satisfy the full empty-aware weak-equivalence property. This proves
coproduct closure, with no pushout or global realization gluing conclusion.

## Independent evidence

The isolated first-`LEAN_PATH` overlay is
`logs/weak-assembly-independent-20261009/olean`. Reviewed compiled artifacts
were excluded before the fresh source builds. Unchanged dependencies are
symlinked into the overlay. The source and key dependency manifests are
checked before and after the build/audits; the compiler uses shared slot1
and one Lean thread.

`audits/WeakCoproductAssemblyIndependentAudit.lean` fixes all six defining
origins, including private/generated declarations, and recursively permits
only `propext`, `Classical.choice` and `Quot.sound`. Its 17 consumers also
import `Quillen.Library`, testing complete path/source formulas, the
original comparison factorization, arbitrary finite degrees, explicit
zero, component surjectivity, empty indices and empty summands.

Evidence is recorded under `logs/weak-assembly-independent-20261009/`;
script `logs/verify-weak-assembly-independent.sh`.

Terminal logs: `check.log`, `WeakCoproductAssembly-audit.log`,
`WeakCoproductAssembly-deps.log`, `WeakCoproductAssembly-hashes-after.log`,
and `prerequisites-after.log` in that evidence directory.
Artifact manifest: `logs/weak-assembly-independent-20261009/artifacts.sha256`.
