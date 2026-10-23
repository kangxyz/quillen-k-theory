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
| `QuillenTest/` | In-package mathematical and interface tests |
| `examples/downstream/` | Independent mathematical example package; explicit diagnostics only |
| `scripts/` | Thin native entry, source discovery, thematic generation and explicit cache setup |
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

Mathlib's native `mk_all --lib Quillen` owns the complete production root.
The Python generator discovers the source graph and creates whole-topic facades. It preserves manually maintained selected entrypoints,
including `Quillen.AlgebraicGeometry.Scheme` and `Quillen.Resolution`.
An existing nested facade opts into generation through its ownership marker;
nested directories alone do not request a facade. New subjects with actual
source are discovered without editing a registry.

The generated production root imports every library module. The native entry
library and disjoint `QuillenModules` library use explicit globs and empty
`roots`; final commands therefore pass `Quillen` explicitly. In-package tests
use `QuillenTest.+` globs without a generated Test umbrella. Clients can use a
smaller individual module or topic import. The Python generator wraps long import
lines and always writes `set_option linter.style.longFile 0` in import-only
facades, including newly discovered subjects. Growing imports therefore need no
recalculated line allowance; implementation limits and other style linters
remain enabled. CI checks generation
against the current source graph. See [CONTRIBUTING.md](../CONTRIBUTING.md) for
extension rules.

## Native local and CI checks

During proof iteration use `lake --rehash build +MODULE` in the prepared
workspace. At final validation, `bash scripts/check.sh` forwards to the shared
native CLI with production root `Quillen` and the existing layout/placeholder
source checks. Install the current `lean-incremental-ci` package or explicitly
select an Aglib tooling checkout using `LEAN_CI_TOOLING_ROOT`. Tooling is
independent of mathematical Lake dependency pins. There is no local adapter,
plan/source/native/finalize protocol, hosted-baseline lookup or recipe-hash gate.

The local native sequence matches public CI: incrementally build production,
prepare native checkers, run the configured `lake test`, check generated entries
with Mathlib `mk_all`, run Mathlib text style and native lint with explicit
production roots, and invoke the pinned upstream production axiom auditor.
The duplicate local Lean linter and audit implementations are removed. Builtin
lint and the configured Batteries driver retain their native argument and
package scopes; text style reads the production entry's import list.

A nonempty documentation-only source comparison runs static checks without Lean
setup. Clean/no-change checks still request native final validation.
`--source-only` explicitly requests static coverage; `--list` prints commands
without execution. `--full` uses the same incremental graph and predicates, with
no forced recompilation, kernel replay or additional acceptance stages.
Independent downstream examples remain available only as explicitly requested
separate diagnostics; ordinary checks never prepare or build that package.
[CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks) owns exact local commands.

Public CI retains three jobs. Build compiles only mathematical production
outputs and saves/stages them independently of checks. Test restores that run's
production artifact, verifies it without compilation, prepares its own checker
tools and performs all required tests/lint/generated-entry/axiom checks. Publish
requires successful Build and Test on a trusted default-branch push. Both jobs
retain completed native compilation on failure; a cache artifact alone is not a
check pass. Local runs have no job-transport or publication lifecycle.

Native Lake traces and artifact caches decide what needs rebuilding. Preserve
matching artifacts and compatible per-command successes after repairs. A merge,
commit, missing receipt or different checkout does not itself require a clean
build, dependency replay or a new audit chain. Local command reuse binds actual
source/native/checker inputs, imports and toolchain; changed, failed or partial
work cannot supply a pass. `--outputs` delivers mappings from the native build
without compiling again. Mapping delivery describes compilation/recovery and
adds no lint, audit or mathematical coverage.

## Mathematical trust

The shared entry uses the pinned upstream `axiom-audit` on built production
roots. It loads their import environment and selects declarations by defining
module under `Quillen`, including loaded private/generated declarations and
those with a different mathematical namespace. It follows axiom dependencies
and allows only `propext`, `Classical.choice` and `Quot.sound`; `sorryAx`, custom
assumptions and native-computation axioms are outside this allowlist. A root
that imports no auditable declarations fails. In-package deliberate negative
fixtures are not production audit roots.

The auditor relies on the prior successful build and trusted compatible
artifacts. It does not recheck imported proofs, establish source correspondence
or certify mathematical interpretation. Source checks retain production/test
separation, local imports/cycles, thematic facade enrollment and placeholders;
native `mk_all` checks complete production-root enrollment. Independent
mathematical review and writing acceptance retain their governing requirements,
and conditional theorems retain their explicit premises.
