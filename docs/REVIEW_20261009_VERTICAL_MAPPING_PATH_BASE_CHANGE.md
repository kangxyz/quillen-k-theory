# Independent review: exact vertical-path base change and lifting

Accepted 2026-10-09 12:36:51 UTC.

## Frozen source scope

- `Quillen/Topology/FiberwiseMappingPath/BaseChange.lean`
- `Quillen/Topology/FiberwiseMappingPath/BaseChangeLifting.lean`

Manifest: `logs/fiberwise-mapping-path-base-change-sources.sha256`.
Both sources were read completely and remain unchanged. This is a post-12:10
archive boundary.

## Semantic assessment

The new source and target are the actual strict pullbacks over the supplied
continuous map `g:T→B`. The new map keeps `t` and applies the original `f` to
the other coordinate. It is not a chosen comparison map.

The homeomorphism identifies a vertical path for this actual pulled-back
map with its new base point and the entire original vertical path. In the
forward direction, verticality in `T` identifies every stored path's first
coordinate with its starting base point. Combining this with each pullback
equation proves verticality of the original path in `B`. The inverse restores
the constant `T` coordinate at every time, retaining all original `F` path
values. The non-definitional inverse law explicitly proves equality of these
first coordinates at every time. Both continuous-map directions are proved
with the actual compact-open path topology and independent space universes.

Finite cube-boundary lifting transfers using this exact homeomorphism. The
original lifting property supplies the entire original vertical path over
the target cube. The new base coordinate is taken from the supplied target
cube map, and the pullback equation follows from its original endpoint
identity. The boundary first-coordinate equality uses the original lifting
square and stored verticality; the whole second path coordinate uses the
original strict boundary lift. Thus every stored path value is retained.
The endpoint equation holds in both original pullback coordinates.

Weakness of the literal pulled-back map then follows by composing the new
endpoint's genuine finite-boundary-lifting weak property with its actual
constant-path inclusion homotopy equivalence. The exact forward composite
is the original pulled-back map. The stronger original vertical-endpoint
lifting hypothesis is retained; arbitrary weak homotopy equivalences are
not asserted to remain weak under base change.

The subset theorem uses the original restriction homeomorphism and fills the
original cube first. Every endpoint lies in the supplied subset, which
suffices to repack the entire vertical path. It covers arbitrary, smaller,
intersected and empty base subsets, with no openness or HLP assumption.
Source, target, base and replacement-base universes are independent.

## Independent checks

The fresh first-path overlay excludes both target artifact families. It
copies and pins the accepted fresh model2, locality3 and full-over-base3
prerequisites. The fixed origin guard checks **34 = 31 + 3**, recursively
allowing only `propext`, `Classical.choice` and `Quot.sound`.

All **23 consumers** are checked: the authored thirteen plus original base
and source coordinates, exact section/scaling compatibility, every finite
original homotopy map, empty-source control, genuine iterated base change
with an additional independent universe, nested smaller subsets, and full
original boundary-path equality for the transferred lift. The original
thirteen explicitly include degree zero, components, intersections and the
empty subset.

Audit: `audits/VerticalMappingPathBaseChangeIndependentAudit.lean`.
Replay: `logs/verify-vertical-mapping-path-base-change-independent.sh`.
Evidence directory: `logs/vertical-mapping-path-base-change-independent-20261009/`.

This boundary supplies stable exact endpoint lifting. Actual bar/collar
lifting hypotheses, quotient-pushout transport and the final global
Waldhausen fibration theorem remain separate.

## Terminal evidence

Both fresh source checks and the fixed34/all23 audit passed warning-free.
No implementation or consumer repair was needed. The target source hashes,
**3,435 prerequisite-source hashes**, **15,786 dependency-artifact hashes**,
eight copied accepted prerequisite artifacts and project/toolchain pins agree
before and after. Both target artifacts are fresh regular files, with actual
first-path import resolution recorded. No live source or artifact was changed.

- Terminal driver: `logs/vertical-mapping-path-base-change-independent-driver.log`
- Source/import log: `logs/vertical-mapping-path-base-change-independent-20261009/check.log`
- Audit log: `logs/vertical-mapping-path-base-change-independent-20261009/audit.log`
- Evidence manifest: `logs/vertical-mapping-path-base-change-independent-20261009/artifacts.sha256`
