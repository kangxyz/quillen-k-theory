# Source layout

Implementation modules follow their mathematical objects and interfaces. The
existing canonical paths and declaration namespaces are retained from the
supplied checkpoint; the complete root and new family imports are generated.

## Entry points

```lean
import Quillen                         -- complete generated library
import Quillen.Library                 -- selected public K/G interfaces
import Quillen.Scheme                  -- selected geometric interfaces
import Quillen.Resolution              -- selected finite-resolution interfaces
import Quillen.CategoryTheory          -- whole subject, generated
import Quillen.Topology                -- whole subject, generated
import Quillen.KTheory                 -- whole subject, generated
```

Focused imports remain the best choice for a small consumer:

```lean
import Quillen.CategoryTheory.ExactCategory.Basic
import Quillen.KTheory.API
import Quillen.Localization.Serre.LocalizationTheorem
```

## Tree

```text
quillen-k-theory/
├── Quillen.lean
├── Quillen/
│   ├── Library.lean, Scheme.lean, Resolution.lean
│   ├── <Subject>.lean                generated optional family imports
│   ├── Algebra/                      algebraic foundations
│   ├── CategoryTheory/               exact categories, Q, small models, A/B
│   ├── Topology/                     realization, homotopy, fibers, HELP
│   ├── KTheory/                      K-groups, functoriality, comparisons
│   ├── Devissage/                    filtration and inclusion comparisons
│   ├── Localization/                 connective Serre localization
│   ├── GTheory/                      finite modules and support
│   ├── Scheme/                       sheaves, bundles, geometric K/G
│   ├── Resolution/                   admissible resolution comparisons
│   ├── PerfectComplexes/             strict and locally-perfect models
│   ├── Waldhausen/                   S-construction and comparisons
│   └── Examples/                     mathematical examples
├── audits/                           trust checks and regression probes
├── examples/downstream/              independently configured Lake client
├── scripts/                          generation and structural checks
├── docs/                             current guides and mathematical notes
│   └── history/                      historical checkpoint reports
├── CONTRIBUTING.md
├── LICENSE
├── lean-toolchain
├── lakefile.toml
└── lake-manifest.json
```

This is the present tree, not a fixed allowed-directory list. A new family or
subtopic can be added when it has an actual mathematical consumer.

## Generation and migration

Run `python3 scripts/generate_imports.py` after source-tree changes. Its
`--check` mode and `scripts/check_library_layout.py` detect stale entries and
unresolved/cyclic imports. Source modules are all enrolled in the complete
entrypoint; tests and clients are outside the production graph.

`module-migration.json` is historical reference for earlier flat implementation
paths. Normal development is not gated on its proof hashes or an immutable
checkpoint inventory. Old implementation aliases remain removed, except that
`Quillen.KTheory` now intentionally names a generated whole-topic import rather
than the earlier flat implementation. Current declarations keep their existing
namespaces such as `Quillen.ExactStructure` and `Quillen.ExactFunctor`.

See [ARCHITECTURE.md](ARCHITECTURE.md) and
[CONTRIBUTING.md](../CONTRIBUTING.md) for dependency and API evolution rules.
