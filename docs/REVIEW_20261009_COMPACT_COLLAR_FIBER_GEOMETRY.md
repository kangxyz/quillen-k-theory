# Independent review: actual double-cylinder fibers and collar HELP

Accepted 2026-10-09 12:57:36 UTC.

## Frozen sources and scope

- `Quillen/CategoryTheory/TheoremB/DoubleCylinderFiberCoordinates.lean`
- `Quillen/CategoryTheory/TheoremB/CollarFiberCoordinates.lean`
- `Quillen/CategoryTheory/TheoremB/CompactCollarFiberComparison.lean`
- `Quillen/CategoryTheory/TheoremB/CompactCollarHomotopyFiberInput.lean`

Manifest: `logs/compact-collar-fiber-geometry-sources.sha256`.
All four sources were read completely. Their production bytes and live
artifacts remain untouched. The accepted fresh `CompactCollarFibers` artifact
is copied and pinned in the independent first-path overlay. This boundary
is after the immutable 12:10 archive freeze.

## Semantic assessment

### Exact endpoint and interior fiber coordinates

The two endpoint embeddings are inherited from the actual pushout of the
closed embedding of both cylinder endpoints, composed with the corresponding
sum inclusion. They do not require the attaching maps to be injective.
Every height-zero point is proved to lie in the original left endpoint
image, and every height-one point in the original right endpoint image,
using actual pushout representatives and the literal height formula. The
opposite endpoint case is excluded by `0 ≠ 1`.

For a map of double cylinders, height preservation locates every point of
an endpoint fiber in the source endpoint image. Injectivity of the target
endpoint embedding gives its exact original endpoint-fiber equation.
The restricted endpoint map is an embedding and is genuinely surjective,
so its homeomorphism has the original endpoint inclusion as its forward map.

At an interior height, the accepted genuine open product chart supplies the
source representative. Injectivity of the target open chart identifies
both its original attaching-object coordinate and its unchanged height.
The fixed-height coordinate map is an embedding, and the same argument
proves surjectivity. This gives the actual interior-fiber homeomorphism
with forward value `l(x,t)`. No fiber is interchanged with a pushout.

### Exact collar restrictions and comparison identities

The collar-fiber homeomorphisms only forget or restore the extra collar
membership proof. Height preservation and the supplied target point prove
that membership; both underlying maps are unchanged. Composing these with
the endpoint and interior coordinate homeomorphisms gives the exact collar
coordinates, with the original endpoint inclusions and cylinder points
as forward maps.

The target of each comparison fiber is the strict fiber of the genuine
endpoint pullback. Its existing exact fiber homeomorphism identifies it with
the original endpoint fiber. At an endpoint, the full comparison becomes
the identity. At an interior point, it becomes precisely the original
attaching-square map between strict fibers, with underlying value `f x`
or `g x`. The required equalities are proved using the original collar
projection formulas. Compact HELP is transported through these genuine
homeomorphisms by its established two-of-three laws.

The all-point proof performs actual height cases. A left-collar point either
has height zero or has height strictly between zero and one; a right-collar
point either has height one or lies in that interior. The cutoff hypotheses
and interval bounds prove these alternatives, including the extreme permitted
cutoffs. There is no missing endpoint or degenerate-height case.

Consequently every collar comparison fiber has full compact HELP from the
original attaching strict-fiber HELP hypotheses. Applying the separately
accepted collar transport theorem discharges its formerly explicit per-point
comparison-fiber premise. The resulting maps are exactly the original
strict-fiber inclusions into the original collar homotopy fibers.

### Original homotopy-fiber input

The companion defines the literal maps induced by the original attaching
squares on the original homotopy fibers. The point is sent by `f` or `g`;
the whole stored path is postcomposed with `f′` or `g′`. The squares with the
original strict-fiber constant-path inclusions commute definitionally.

Actual HLP of the relevant vertical maps makes those strict-fiber inclusions
genuine homotopy equivalences. Composition and cancellation of their compact
HELP therefore transfer the supplied original homotopy-fiber-map HELP to the
required original attaching strict-fiber maps. This discharges the geometric
input without assuming the desired collar conclusion. The left result uses
HLP of `a,b`, and the right result uses HLP of `a,c`, together with the
corresponding original homotopy-fiber HELP for every attaching base point.

The full original prescribed boundary track is retained by compact HELP,
not merely its endpoints. All spaces use the explicit common-universe
contract of the existing TopCat/HLP/HELP API. No separation, nonemptiness,
continuous family of inverse maps, or HLP of an original collar is assumed
or inferred.

## Independent checks

The fresh first-path overlay excludes all artifact families of the four
targets. They are rebuilt in dependency order, and actual fresh imports are
verified. A single module-origin traversal recursively checks the fixed
**92 = 25 + 40 + 16 + 11** declarations against only `propext`,
`Classical.choice` and `Quot.sound`.

The audit checks the exact endpoint/interior forward maps and inverse laws,
literal collar forget/restore coordinates, empty extreme-cutoff collars,
actual identity-versus-attaching-map comparison formulas, both complete
height-case conclusions, unchanged homotopy-fiber paths and strict-inclusion
squares, and both full prescribed-boundary HELP outputs.

Audit: `audits/CollarFiberComparisonIndependentAudit.lean`.
Replay: `logs/verify-compact-collar-fiber-geometry-independent.sh`.
Evidence directory: `logs/compact-collar-fiber-geometry-independent-20261009/`.

## Remaining scope

This proves the original collar strict-to-homotopy-fiber inclusions have full
compact HELP under the stated original edge-fiber hypotheses. It does not
prove HLP of collar projections or variable-base lifting, interchange fibers
with quotient pushouts, or complete global bar/Waldhausen fibration gluing.
Those are separate obligations, not consequences silently inferred here.

The first fresh-source audit passed all 92 origins and 50 exact-map consumers.
The final audit additionally imports the accepted compact-HELP weak-equivalence
consumer layer and tests both original collar maps in every finite degree,
degree zero separately and on components. An audit-only line break before
a dotted projection was initially parsed as a new function argument; it was
corrected without changing any implementation source or mathematical claim.
The diagnostic is retained in the evidence directory. The four fresh target
artifacts are pinned and rechecked across the final audit.

## Terminal result

The fresh4 rebuild and final fixed92/all56 consumer audit passed warning-free.
No production change was needed. All source hashes, **3,414 prerequisite-source
hashes**, **15,758 dependency-artifact hashes**, the accepted copied collar
prerequisite, four fresh target artifacts and project/toolchain pins agree
before and after. The four targets are regular fresh artifacts with actual
first-path import resolution recorded. The initial 50-consumer dependency
manifests are retained separately; the expanded final audit additionally pins
the accepted compact-HELP weak-equivalence consumer layer.

- Terminal driver: `logs/compact-collar-fiber-geometry-independent-terminal-driver.log`
- Fixed audit: `logs/compact-collar-fiber-geometry-independent-20261009/audit-fixed92.log`
- Final replay: `logs/finalize-compact-collar-fiber-geometry-independent.sh`
- Evidence manifest: `logs/compact-collar-fiber-geometry-independent-20261009/artifacts.sha256`
