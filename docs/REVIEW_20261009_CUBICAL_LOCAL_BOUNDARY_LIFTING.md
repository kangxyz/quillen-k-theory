# Independent review: genuine local finite-boundary lifting

## Scope and current status

The frozen four-source scope is `Topology/CubicalSubdivision/{BoundaryLifting,
LocalLifting,FiberBoundaryLifting}.lean` and
`Waldhausen/Fibration/RelativeRows/CubicalLifting.lean`. The manifest
`logs/cubical-local-lifting-sources.sha256` has fingerprint
`cbcb3a401367643f129386d2e671d8c18b579f256e693d82586bd9f7a003554d`.

**Accepted.** Complete semantic inspection, four fresh excluded-target builds
and the fixed-15 recursive-origin audit with all 19 strengthened consumers
passed warning-free. Source, prerequisite and toolchain hashes match before
and after; terminal validation completed at 11:36:48 UTC on 2026-10-09. No production source is changed. The
future direct weak-equivalence bridge and global weak-cartesian gluing are
outside this source scope.

## Original lifting property and face adapter

`BoundaryLifting p` is exactly strict lifting against each original finite
cube boundary: arbitrary continuous maps a on the whole boundary and b on
the cube, satisfying p a = b there, admit c with both c on the boundary equal
to a and p c = b. Source and target universes are independent. No homotopy-set
bijection, weak-equivalence conclusion, or arbitrary-compact HELP property
is a hypothesis or part of the definition.

The categorical adapter uses actual lifted-boundary RLP in a common universe
and removes only `ULift` from the parameters. Its boundary and target maps
are literal coordinate maps; the two factorization equations of the actual
categorical square give the original strict equations.

The face-coordinate adapter uses the already proved actual parameter and
whole-boundary homeomorphisms. Their forward and inverse coordinates commute
exactly with subtype inclusion. Transporting the strict square and its lift
therefore retains the entire original face-boundary map. The dimension-zero
case uses an actually empty boundary, not a pointed or nonempty substitute.

## Genuine locality on an open target cover

`restriction p U` has literal source `{e // p e ∈ U}`, target U, and map
`e ↦ ⟨p e.val,e.property⟩`. The locality theorem assumes `BoundaryLifting` for
these actual restrictions, for an open cover of the entire target. The
source, target and cover-index universes are independent.

For each specified cube test, one actual finite grid is chosen subordinate
to the pullback cover, controlling whole faces in all dimensions. The
induction constructs a strict lift on the lower face skeleton and also
retains every originally prescribed outer-boundary value.

The initial lower skeleton is empty. At each stage an outer face uses the
given boundary map itself. A non-outer face is assigned one chart containing
its whole image. The existing boundary lift belongs to the source restriction
because its projection is exactly the specified test map; thus the genuine
local face RLP applies. Its full attaching boundary is retained. Every point
of a non-outer face on the original outer boundary is already on that
attaching boundary, so the original boundary values persist. The accepted
actual quotient-pasting theorem gives a continuous next-stage map retaining
all these values and its exact projection. At stage n+1 the lower skeleton
is the whole original cube.

No HEP for an arbitrary closed inverse-image subset is used. All geometric
attachments are the actual finite face boundaries already constructed.
Choices of charts and fillers are ordinary existential choices of finitely
many maps; no continuously chosen family of inverse maps is assumed.

The dimension-zero lifting consumer gives actual point-surjectivity of p.
Consequently an empty source cannot satisfy the property with a nonempty
target. This is tested independently, beyond the raw zero-dimensional square.

## Literal fiber and relative-row endpoints

The generic fiber adapter assumes actual HLP for two projections over one
base, a displayed map over that base, and full compact HELP for its original
strict-fiber maps. The compact lifted cube, its genuine whole-boundary HEP
and its actual contraction are supplied to the accepted full contracted-test
HELP theorem. The accepted pair-HELP-to-mapping-path-RLP theorem then proves
`BoundaryLifting (MappingPath.endpoint f)`. It asserts the lifting property
of that literal endpoint map, not strict RLP of f itself.

For a strict square, the actual mapping-path replacement projections are
genuine fibrations. Original full path-space fiber HELP is transported to
their strict fibers using the existing exact fiber homeomorphisms. The
normalized endpoint therefore retains the original source and base maps and
full path coordinates.

The relative-row result supplies all those fiber premises from the genuine
nested-weak-equivalence structure N and the previously accepted row
additivity/path-transport results. Its conclusion is exactly
`BoundaryLifting (MappingPath.endpoint (rowNormalizedComparison N α))`.
The common model universe is explicit: `C : Type u`, `Category.{u} C`.
No local or global comparison equivalence is assumed to construct this input.

## Important remaining distinction

The locality theorem requires RLP for the actual restrictions of its specified
map p. If p is a global mapping-path endpoint, membership in the restriction
constrains the endpoint, not every point along the stored path. Forming the
mapping-path endpoint of a chart-restricted original map produces a different
space whose paths stay in that chart. This review does not identify those
two constructions or supply the missing local restriction lifts by fiat.

The checked results prove genuine finite-boundary RLP locality and the stated
original normalized-row endpoint input. They do not convert finite-boundary
RLP to full HELP on arbitrary compact HEP pairs, nor establish global
weak-cartesian collar gluing or the connected-row diagonal fiber theorem.

## Independent checks

All artifact families of the four targets are excluded from the first-path
overlay before fresh compilation. Direct dependency output checks use of the
new regular target `.olean` files. The evidence hashes all four targets,
3,637 recursively resolved prerequisite sources, 16,259 prerequisite
artifacts, and project/toolchain pins before and after source and audit runs.
The mutable public umbrella is outside this frozen prerequisite closure;
the consumer audit still includes `Quillen.Library` for collision detection.

The fixed-15 audit traverses every declaration's actual defining origin,
including private/generated declarations (BoundaryLifting 7, LocalLifting 5,
FiberBoundaryLifting 2, RelativeRows/CubicalLifting 1), and recursively permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The 19 consumers include independent universes, the literal open restriction,
all-degree and explicit zero-dimensional original lifting squares, strict
point-surjectivity and empty-source consequences, forward/inverse raw face
coordinates, full face-boundary preservation, original fiber and normalized
square endpoints, the exact original row-map expression and its full mapping-
path coordinates. The zero-dimensional row test gives its target subtype
explicitly.

Audit: `audits/CubicalLocalLiftingIndependentAudit.lean`.
Preparation: `logs/prepare-cubical-local-lifting-independent.py`.
Replay: `logs/verify-cubical-local-lifting-independent.sh`, with `build`
and then `audit` arguments.
Evidence: `logs/cubical-local-lifting-independent-20261009/`.

## Frozen source hashes

- BoundaryLifting: `7e75d9557a577ff59fdc7c54bd8bff00df5b8682ae06eb8cb745bc261bf0d285`
- LocalLifting: `eb072ea6af0edf7aa7651ee265af60f381119ca9ac18cd50054aedbec47863d8`
- FiberBoundaryLifting: `039705c1f2ba28d402b1c587d2422b7e5d0189bbc4b69739cdddfe62c1aea844`
- RelativeRows/CubicalLifting: `14530aba1536f4018ec175a50243843add2983a2b61b7d886b6d17ecf0dcdb4f`

The Lean source and consumer checks needed no repair. The final shell
import-resolution assertion was broadened from direct audit imports to both
the audit and fresh source dependency output, since BoundaryLifting is
imported transitively by the audit. The completed source/audit run and
after-hash logs were preserved; validation was resumed without a duplicate
Lean run by `logs/resume-cubical-local-lifting-independent-validation.sh`.

Terminal drivers: `logs/cubical-local-lifting-independent-build-driver.log`
and `logs/cubical-local-lifting-independent-audit-driver.log`.
Evidence manifest: `logs/cubical-local-lifting-independent-20261009/artifacts.sha256`.
