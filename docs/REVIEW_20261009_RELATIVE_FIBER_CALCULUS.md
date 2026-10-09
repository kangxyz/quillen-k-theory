# Independent review: compact HELP and actual fiber detection

Accepted on 2026-10-09 after complete semantic inspection, ten fresh isolated
source builds, a fixed39 recursive-origin audit, twenty-seven exact consumers,
and before/after source and dependency hash checks. All final checks passed
warning-free. The scope is exactly the ten frozen sources in
`logs/relative-fiber-calculus-sources.sha256`.

## Mathematical boundary

### Compact HELP retains the whole boundary

`CompactHomotopyExtensionLiftingProperty` quantifies over actual compact
TopCat pairs and the ordinary homotopy extension property. Its conclusion
requires both an exact lift on the included subspace and equality with the
entire supplied boundary homotopy, at every time and boundary point.

`compactHELP_of_injective_compact_lifts` derives this property from injectivity
and genuine continuous exact lifts of compact-source maps. It lifts both the
ambient map and the original boundary homotopy. Injectivity identifies the
lifted boundary endpoints. Ordinary HEP extends the reversed lifted boundary
homotopy; reversing the resulting ambient homotopy then gives the original
boundary path exactly. There is no comparison-equivalence hypothesis.

Composition is also genuine. The two successive HELP applications initially
give a constant prefix on the boundary. The proof uses the existing relative
interval-square extension to remove this prefix while retaining both global
endpoint maps. I read both the composition proof and the boundary-correction
implementation; the conclusion does not silently reparameterize the requested
boundary data.

The actual canonical realization-product comparison has exact compact-source
lifts in an independent parameter universe. The proof factors only the second
coordinate through an actual finite subcomplex and uses the established
finite-right realization-product homeomorphism there. It makes no unrestricted
ordinary-product realization homeomorphism assertion. Its compact HELP follows
from these exact lifts and the original comparison's proved injectivity.

The corresponding source-change homotopy-fiber lift preserves the supplied
path coordinate literally. It lifts only the source coordinate and checks both
original endpoint equations. The unrestricted parameter-universe lemma has
independent source, target, base and parameter universes. The bundled compact
HELP statements use the common universe required by the existing HELP API.

### Split row fibers preserve original maps and paths

`SplitRealizationFiber` takes an actual simplicial map `χ : E → A ⊗ B`, a
genuine homotopy equivalence whose forward continuous map is exactly its
realization, and a strict splitting triangle `s ≫ χ = vertexSection A B y`.
These are the genuine product-comparison inputs, not a fiber-equivalence
conclusion supplied as an assumption.

The source-change comparison retains the original path. Its actual homotopy
equivalence is constructed from the given row comparison with that exact
forward map. `firstProjection` is the original realized first projection on
the fiber's source coordinate. Its all-degree bijectivity and compact HELP
follow by composing the accepted product-fiber results with this genuine
source-change equivalence.

The original split inclusion is `|s|` equipped with the constant path at the
specified realized vertex. Its whole source/path pair is identified with the
original product-fiber inclusion. Cancellation against the genuine comparison
proves bijectivity of this exact inclusion in every finite degree, including
zero. No inverse family over varying points is selected or assumed.

### LES detection includes the pointed-set branch

For an actual map `m : X → Y` over one unchanged base, `mapOver` is the original
homotopy-fiber map induced by `(m,id)`. It changes the source coordinate by
`m` and retains the original base path.

For each `n ≥ 0`, bijectivity of this fiber map in degree `n+1` and injectivity
in degree `n` imply bijectivity of the original `piMap n m`, i.e. the original
map in degree `n+1`. The proof is a diagram chase in the actual homotopy-fiber
LES. Injectivity uses the original connecting homomorphism one degree above.
Surjectivity uses exactness of the original connecting set-map, then corrects
a lift by an actual fiber class. The correction order works for the potentially
noncommutative fundamental group.

At `n=0`, the surjectivity argument invokes the original function
`π₁(base) → π₀(fiber)` and only its constant-class criterion plus injectivity
of the original fiber map on π₀. It introduces no group structure on π₀.
The final all-degree detection theorem assumes actual path connectedness of
both total spaces to handle degree zero; the separately proved path transport
then propagates the result to every source point.

### Actual connectedness is derived where claimed

Injectivity of an actual π₀ map into a path-connected space proves the source
path-connected, using its specified point for nonemptiness and the actual
`pi0EquivZerothHomotopy`. This gives connectedness of nonempty product-type
fibers when the genuine first factor is path-connected.

A genuine Hurewicz fibration over a path-connected base has path-connected
total space if one actual strict fiber is path-connected. The proof lifts a
base path separately from each total-space point and joins its endpoint within
that strict fiber. It makes no continuous choice of those paths. The homotopy-
pullback specialization uses the existing actual base-projection fibration and
the explicit homeomorphism of its strict fiber with the original homotopy fiber.

## Scope and limits

Generic LES detection and zero detection permit independent object universes.
Exact compact lifting permits an independent compact parameter universe.
Simplicial realization, bundled HELP, and the Hurewicz connectedness wrappers
use the common universes stated by their existing interfaces.

The reviewed sources are concrete relative-fiber prerequisites. They contain
no global diagonal-fiber theorem, weak-Cartesian pushout gluing theorem,
skeletal/sequential assembly, or unrestricted Whitehead upgrade. All
`TwoSidedBar*` drafts and `CartesianDetection.lean` are outside this boundary.
No conclusion from those unfinished sources is imported or used.

## Verification evidence

Independent source manifest:
`logs/relative-fiber-calculus-independent-20261009/sources.sha256`.
Manifest SHA-256:
`1f45713d33b69e4d15289631f55375b4384ed73167837d0623cf7e804bb891e9`.

All ten selected artifact stems were excluded from the fresh overlay before
compilation. Each selected `.olean` is newly built, not a symlink. Only unchanged
prerequisite artifacts are linked. The overlay is first in `LEAN_PATH`; direct
import resolutions are retained in `deps.log`. No production source or artifact
was changed by this review.

Evidence directory: `logs/relative-fiber-calculus-independent-20261009/`.
- `check.log`: ten warning-free fresh ordered source checks
- `deps.log`: selected fresh direct import resolutions
- `hashes-before.log`, `hashes-after-build.log`, `hashes-after-audit.log`
- `dependency-sources.sha256` and before/after dependency hashes
- `accepted-dependency-hashes.log`: unchanged accepted product7, fiber4 and path-transport manifests
- `audit-final.log`: final count-frozen recursive-origin and exact-consumer check
- `artifacts.sha256`: exact report, audit, scripts, logs and fresh artifacts

The independent audit is `audits/RelativeFiberCalculusIndependentAudit.lean`.
Its twenty-seven consumers retain the full HELP boundary homotopy, literal
fiber paths and original maps, the original split source and constant path,
arbitrary universes, the explicit π₁-versus-π₀ LES branch, actual zero-degree
bijections, all-source-point detection and genuine Hurewicz connectedness.
The fixed39 audit enumerates all defining-module declarations, including
private/generated ones, and recursively found only `propext`, `Classical.choice`,
and `Quot.sound`. Per-module origin counts are SplitFiber16, CompactLifting1,
ProductCompactHELP2, Composition1, fiber CompactHELP2, GroupDetection5,
ZeroDetection3, ProductFiberHELP5, FiberDetection2 and Connected2.

The build and audit scripts acquire shared slot1 and record acquisition times.
This boundary is outside the previously frozen 08:05 archive.
