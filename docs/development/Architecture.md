# Architecture

The library is organized by mathematical objects and reusable interfaces.
Source ownership and import dependencies support extension without a fixed
list of future topics. The [documentation map](../README.md) connects the current
reader guides and references.

## Source boundaries

| Location | Purpose |
| --- | --- |
| `Quillen/` | Reusable mathematics |
| `Quillen/Aglib/` | General-theory candidates prepared for later upstream admission |
| `Quillen.lean` | Generated complete import surface |
| `Quillen/<Subject>.lean` and owned nested facades | Whole-topic or selected public imports |
| `QuillenTest/` | Maintained tests and exhaustive library axiom audit |
| `examples/downstream/` | Independently configured client package and audit |
| `Tools/` and `scripts/` | Lint, source discovery, generation, cache, and checks |
| `docs/topics/` | Mathematical guides organized by objects and comparison families |
| `docs/reference/` | Shared API and mathematical scope references |
| `docs/development/` | Source architecture and measured typechecking performance |

QuillenTest, tools, and clients depend on the library. Implementation source imports
individual dependencies, avoiding broad facades. The structural checker rejects
cycles and reverse dependencies on tests, tools, or clients.

Accepted shared algebra, exact-category, module-sheaf and cohomology interfaces
are owned by Aglib. Further general implementations live in the local
[Quillen/Aglib candidate tree](../../Quillen/Aglib/README.md), under their intended
mathematical subjects. Specialized applications import these focused leaves.
Relocation preserves existing declaration names and chosen maps; a candidate
module prefix does not assert upstream admission. Each declaration has one local
implementation, and mixed sources keep only their specialized application part.

## Mathematical owners

| Owner | Principal objects and interfaces |
| --- | --- |
| `Aglib/Algebra`, `Aglib/CategoryTheory`, `Aglib/RingTheory` | General module and homological algebra, exact-category foundations, filtrations/resolutions, regular-local rings, and finite-defect constructions |
| `Algebra` | Stable matrix groups and application-specific algebraic constructions |
| `Aglib/LinearAlgebra` | Generic product identities and finite matrix constructions |
| `CategoryTheory` | Q-construction, exact-category applications, small-model K-theory, categorical localization, and Theorems A/B |
| `Topology` | Based homotopy, fibers and cylinders, lifting, realization, prespectra, stable fibers, and categorical stable localization |
| `KTheory` | Exact-category K-groups, canonical maps, and generic Bass diagrams and cokernel recursion |
| `KTheory/Plus` | Projective group completion, original ring plus/Q comparison, ring-change naturality, and component classification |
| `Devissage`, `Resolution`, `Localization`, `GTheory` | Filtration and resolution comparisons, localization, and finite-module G-theory |
| `Aglib/AlgebraicGeometry` | General scheme, module-sheaf, cohomological and perfect-complex candidates |
| `AlgebraicGeometry/Scheme` | Scheme K/G interfaces and specialized projective-line applications |
| `AlgebraicGeometry/PerfectComplexes` | Waldhausen/K-theory models, localized spectra, Bass groups and specialized applications |
| `Waldhausen` | Waldhausen structures, S-construction, additivity, approximation, cofinality, fibration, and comparisons |

Categorical constructions and topology interact; subject directories do not
impose a total order on dependencies. Generic topology belongs in `Topology`,
including reusable foundations used by Theorem B. Generic approximation and
functorial factorization interfaces are independent of the split-complex model.
Twisted singular chains and local-system homology belong in
`Topology/LocalCoefficients`; action localization and monoidal group completion
belong in `CategoryTheory/GroupCompletion`. The ring-specific plus comparison
consumes those foundations and the finite-projective module constructions.

Finite-module category foundations and finite-projective resolutions belong in
`Aglib/Algebra/Category/ModuleCat` and `Aglib/Algebra/Homology`; their G-theory
localization consumers remain in `GTheory`. Regular-local ring arguments belong
in `Aglib/RingTheory/RegularLocalRing`, while the canonical scheme K-to-G comparisons remain in
`AlgebraicGeometry/Scheme/Regular`. Shared realization, interval, simplex and
arrow lemmas live below the theorem-specific constructions that use them.
Chart selectors and open pullback squares are owned by the existing chart and
sheaf interfaces, rather than repeated in their applications.

A module's path records its owner. Its declaration namespace should describe
the mathematical construction and need not mirror the path. Geometric interfaces
use `AlgebraicGeometry.Scheme` and `Quillen.PerfectComplexes`; generic constructions have
their own canonical namespaces. See [the API reference](../reference/API.md#module-paths-and-namespaces).

## Import generation and extension

The generator discovers the source graph and creates the complete root and
whole-topic facades. It preserves manually maintained selected entrypoints,
including `Quillen.AlgebraicGeometry.Scheme` and `Quillen.Resolution`.
An existing nested facade opts into generation through its ownership marker;
nested directories alone do not request a facade. New subjects with actual
source are discovered without editing a registry.

The generated root imports every library module. Clients can use a smaller
individual module or topic import. The generator wraps long import lines and
gives oversized import-only facades a local long-file bound derived from their
generated size; the other style linters remain enabled. CI checks generation
against the current source graph. See [CONTRIBUTING.md](../../CONTRIBUTING.md) for
extension rules.

## Trust checks

`scripts/check.sh` provides explicit comprehensive diagnostics and declared CI
coverage; it is not a normal local acceptance step. It builds the library and
tests, runs the configured lint checks, and builds the separate downstream
package. It explicitly replays
`QuillenTest/Axioms.lean` and the downstream `Audit.lean`, because cached compiled
modules do not re-execute audit commands.

Normal authoring, maintenance, documentation, review, merge, integration, and
publication must use incremental checks, reusing trusted caches and compatible
existing evidence with new checks for changed or missing required
modules, affected consumers, and changed trust-check inputs. Reconcile combined
changes before reusing coverage. The phase, commit identity, a missing receipt,
or a different checkout alone does not require complete compilation, fresh
dependency replay, or rerunning every audit and source suite. See
[the validation policy](../../CONTRIBUTING.md#tests-and-checks) for cache recovery
and the exceptional fault-recovery conditions for a whole-library rebuild.
Missing coverage alone calls for the uncovered affected checks. Outside fault
recovery, a literal full rebuild or replay requires an explicit user request
with that exact scope.

CI restores root, downstream, and pinned Aglib build outputs and shared native
Lake artifacts. Versioned keys distinguish platform, toolchains, manifests, and
normalized Lake configurations. The configuration hash (`scripts/cache_key.py`,
Python 3.11+) omits only the top-level `version`, `enableArtifactCache`, and
`restoreAllArtifacts` fields of each TOML package configuration. Compiler
options, targets, metadata, and nested dependency versions remain part of it.
Toolchains, manifests, and optional executable Lake configurations are hashed
raw; invalid or missing required configuration fails visibly. A configuration
key change selects matching artifacts and actual invalidation; it is not a
local instruction to recompile every library.

Project source hashes and source-independent prefixes permit restoration after
source changes. The configured CI job runs `bash scripts/check.sh --ci --rehash`:
Lake validates restored traces against current content and incrementally builds
missing or stale modules and affected dependents. The complete CI checks include
lints and both explicit audits even on exact cache hits. This CI coverage does
not make that command the local merge or publication default. CI saves partial
build progress, while publishing checked native artifacts only after successful
checks. Publication of the native cache consumes those checked artifacts rather
than requiring a fresh proof build.

The exhaustive library audit uses legacy imports to expose transitive private
module declarations. It discovers imported module inventories and local
environment declarations, selects every declaration defined in a `Quillen`
module or in the `Quillen` namespace, deduplicates names, and rechecks defining
origin. Private helpers are included. `collectAxioms` follows transitive
dependencies and rejects any axiom outside `propext`, `Classical.choice`, and
`Quot.sound`.

This audit covers the selected kernel declarations and foundation dependencies.
It does not establish a definition's mathematical interpretation, correspondence
with an external source, or a comparison theorem absent from the library.
