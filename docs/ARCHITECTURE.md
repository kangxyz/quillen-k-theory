# Architecture

The library is organized by mathematical objects and reusable interfaces.
Source ownership and import dependencies support extension without a fixed
list of future topics. The [documentation map](README.md) connects the current
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
| `Quillen/**/README.md` and focused family guides | Mathematical results, API/interfaces, exact hypotheses, consumers and remaining inputs at source owners |
| `docs/` | Global summaries, navigation, compatibility/history, workflow, evidence/provenance and operations |
| `docs/ARCHITECTURE.md`, `docs/PERFORMANCE.md` | Architecture, trust operations and performance; setup/checks remain in `CONTRIBUTING.md` and candidate workflow in `docs/DEVELOPMENT.md` |

QuillenTest, tools, and clients depend on the library. Implementation source imports
individual dependencies, avoiding broad facades. The structural checker rejects
cycles and reverse dependencies on tests, tools, or clients.

Accepted shared algebra, exact-category, module-sheaf and cohomology interfaces
are owned by Aglib. Further general implementations live in the local
[Quillen/Aglib candidate tree](../Quillen/Aglib/README.md), under their intended
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
their own canonical namespaces. See the [source-family guides](../Quillen/README.md) for actual namespaces and interfaces.

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
against the current source graph. See [CONTRIBUTING.md](../CONTRIBUTING.md) for
extension rules.

## Trust checks

The common config entry
`python3 -m lean_ci check --config .github/lean-ci.toml --root .` selects affected
and uncovered checks. CI delegates the shared plan/source/native/finalize lifecycle
to one pinned reusable workflow. Root and downstream packages keep distinct native
build and check identities. Selected-origin axiom checks include private/generated
declarations; cached compiled modules do not re-execute their audit commands.

Incremental validation includes applicable compilation, declaration/text-style
lint, affected `QuillenTest` and client tests, and source/trust checks. Cover the
relevant categories in the task's final validation before delivery, reusing
compatible evidence. During development use incremental compilation and its
diagnostics; independent lint and tests run only at final validation.
Helper returns, internal commits and merges do not trigger them. After repairs,
rerun only failed or newly affected checks. Compilation alone does not supply
separate lint or test coverage.

Normal authoring, maintenance, documentation, review, merge, integration, and
publication must use incremental checks, reusing trusted caches and compatible
existing evidence with new checks for changed or missing required
modules, affected consumers, and changed trust-check inputs. Reconcile combined
changes before reusing coverage. The phase, commit identity, a missing receipt,
or a different checkout alone does not require complete compilation, fresh
dependency replay, or rerunning every audit and source suite. See
[the validation policy](../CONTRIBUTING.md#tests-and-checks) for cache recovery
and the exceptional fault-recovery conditions for a whole-library rebuild.
Missing coverage alone calls for the uncovered affected checks. Outside fault
recovery, a literal full rebuild or replay requires an explicit user request
with that exact scope.

The reusable workflow restores compatible dependency, compiled-output and
per-check progress caches. Its tooling revision is pinned independently of the
mathematical Aglib dependency. The common implementation owns cache identities,
resource limits, old/new affected-scope graphs and check bindings; this repository
provides only [declarative roles](../.github/lean-ci.toml) and mathematical content.
A cache-key change selects matching inputs and actual invalidation; it does not
instruct local users to recompile every library.

The common source/native phases consume one admitted plan. Lake incrementally
builds stale or missing required targets. Check receipts retain compatible
per-origin successes immediately, including across failed invocations. Publication
requires qualified coverage; artifacts alone do not invent a passed lint or audit.
Finalization aggregates results without executing native checkers again.

Declaration lint uses an isolated canonical environment per origin with the
runtime imported before that origin. It cannot reuse the former whole-library or
target-first lint predicate as equivalent coverage. Import-only facade certificates
may omit empty declaration work while preserving source/build coverage. Trust
checks have separate visibility/trust rules, discover selected defining origins,
include private and generated declarations, and reject axioms outside `propext`,
`Classical.choice`, and `Quot.sound`.

This audit covers the selected kernel declarations and foundation dependencies.
It does not establish a definition's mathematical interpretation, correspondence
with an external source, or a comparison theorem absent from the library.
