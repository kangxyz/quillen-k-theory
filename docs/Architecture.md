# Architecture

The library is organized by mathematical objects and reusable interfaces.
Source ownership and import dependencies support extension without a fixed
list of future topics.

## Source boundaries

| Location | Purpose |
| --- | --- |
| `Quillen/` | Reusable mathematics |
| `Quillen.lean` | Generated complete import surface |
| `Quillen/<Subject>.lean` and owned nested facades | Whole-topic or selected public imports |
| `Tests/` | Maintained tests and exhaustive library axiom audit |
| `examples/downstream/` | Independently configured client package and audit |
| `Tools/` and `scripts/` | Lint, source discovery, generation, cache, and checks |
| `docs/` | Reader documentation |

Tests, tools, and clients depend on the library. Implementation source imports
individual dependencies, avoiding broad facades. The structural checker rejects
cycles and reverse dependencies on tests, tools, or clients.

## Mathematical owners

| Owner | Principal objects and interfaces |
| --- | --- |
| `Algebra` | Module complexes, homological algebra, and commutative algebra |
| `CategoryTheory` | Exact categories, Q-construction, small models, categorical localization, and Theorems A/B |
| `Topology` | Based homotopy, fibers and cylinders, lifting, realization, prespectra, stable fibers, and categorical stable localization |
| `KTheory` | Exact-category K-groups, canonical maps, and generic Bass diagrams and cokernel recursion |
| `Devissage`, `Resolution`, `Localization`, `GTheory` | Filtration and resolution comparisons, localization, and finite-module G-theory |
| `AlgebraicGeometry/Scheme` | Sheaves, vector bundles, finite-type/coherent sheaves, scheme K/G interfaces, base products, and projective-line charts |
| `AlgebraicGeometry/PerfectComplexes` | Strict/local models, derived representatives, support, localization, Mayer–Vietoris, localized spectra, and Bass groups |
| `Waldhausen` | Waldhausen structures, S-construction, additivity, approximation, cofinality, fibration, and comparisons |

Categorical constructions and topology interact; subject directories do not
impose a total order on dependencies. Generic topology belongs in `Topology`,
including reusable foundations used by Theorem B. Generic approximation and
functorial factorization interfaces are independent of the split-complex model.

A module's path records its owner. Its declaration namespace should describe
the mathematical construction and need not mirror the path. Geometric interfaces
use `Quillen.Scheme` and `Quillen.PerfectComplexes`; generic constructions have
their own canonical namespaces. See [Library.md](Library.md#module-paths-and-namespaces).

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

`scripts/check.sh` builds the library and tests, runs the configured lint
checks, and builds the separate downstream package. It explicitly replays
`Tests/Axioms.lean` and the downstream `Audit.lean`, because cached compiled
modules do not re-execute audit commands.

CI caches the complete root and downstream `.lake/build` directories across
runs. Versioned keys separate operating systems, architectures, and both
packages' toolchains, manifests, and Lake configurations; a hash of the project
Lean sources permits exact hits for documentation-only changes. A compatible
configuration prefix restores older successful builds after source changes.
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
