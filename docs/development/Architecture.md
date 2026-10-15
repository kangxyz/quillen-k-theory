# Architecture

The library is organized by mathematical objects and reusable interfaces.
Source ownership and import dependencies support extension without a fixed
list of future topics. The [documentation map](../README.md) connects the current
reader guides and references.

## Source boundaries

| Location | Purpose |
| --- | --- |
| `Quillen/` | Reusable mathematics |
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

General algebra, exact-category, module-sheaf and cohomology implementations are
owned by Aglib. Quillen consumers import its exact leaves and native mathematical
names. The transferred compatibility modules and aliases are removed. A Quillen
application may extend a native namespace while remaining defined and audited
as a Quillen module.

## Mathematical owners

| Owner | Principal objects and interfaces |
| --- | --- |
| `Algebra` | Finite-module exact categories and resolutions, module complexes, homological algebra, regular-local ring theory, finite-defect Laurent parametrices, stable matrix groups, and finite-projective scalar extension |
| `LinearAlgebra` | Generic linear product identities used by the module constructions |
| `CategoryTheory` | Q-construction, exact-category applications, small-model K-theory, categorical localization, and Theorems A/B |
| `Topology` | Based homotopy, fibers and cylinders, lifting, realization, prespectra, stable fibers, and categorical stable localization |
| `KTheory` | Exact-category K-groups, canonical maps, and generic Bass diagrams and cokernel recursion |
| `KTheory/Plus` | Projective group completion, original ring plus/Q comparison, ring-change naturality, and component classification |
| `Devissage`, `Resolution`, `Localization`, `GTheory` | Filtration and resolution comparisons, localization, and finite-module G-theory |
| `AlgebraicGeometry/Scheme` | Sheaves, vector bundles, finite-type/coherent sheaves, scheme K/G interfaces, base products, and projective-line charts |
| `AlgebraicGeometry/PerfectComplexes` | Strict/local models, derived representatives, support, localization, Mayer–Vietoris, localized spectra, and Bass groups |
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
`Algebra/Category/ModuleCat` and `Algebra/Homology`; their G-theory localization
consumers remain in `GTheory`. Regular-local ring arguments belong in
`Algebra/RegularLocal`, while the canonical scheme K-to-G comparisons remain in
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

`scripts/check.sh` builds the library and tests, runs the configured lint
checks, and builds the separate downstream package. It explicitly replays
`QuillenTest/Axioms.lean` and the downstream `Audit.lean`, because cached compiled
modules do not re-execute audit commands.

CI caches the complete root and downstream `.lake/build` directories across
runs. Versioned keys separate operating systems, architectures, and both
packages' toolchains, manifests, and Lake configurations. The v2 configuration
hash (`scripts/cache_key.py`, Python 3.11+) parses both `lakefile.toml` files,
removes only their top-level package `version`, and canonicalizes the remaining
typed configuration. Pure package version changes reuse the same configuration
hash; compiler options, targets, metadata, and nested dependency versions remain
part of it. Toolchain and manifest files are hashed raw with their paths;
optional `lakefile.lean` files are conservatively hashed raw, including version
text and file presence. Missing required inputs, malformed TOML, and unsupported
TOML scalars (dates/times or nonfinite floats) fail the hash step visibly.

A hash of the project Lean sources permits exact hits for documentation-only
changes. A source-independent v2 prefix restores successful builds with the
same normalized configuration after source changes. During migration, the
second restore prefix is the legacy v1 key with the exact current raw
configuration hash, including package versions; it never crosses configuration
boundaries to restore an older incompatible build.
`bash scripts/check.sh --rehash` always runs: Lake validates restored traces
against current content and incrementally rebuilds missing or stale modules,
including dependents of changed imports. Both lints and both explicit audits
run even on exact cache hits. Only successful jobs publish new build caches.

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
