# Quillen K-theory in Lean

[![CI](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml)

A reusable Lean library for exact categories, Quillen's Q-construction, connective
algebraic K/G-theory, and their categorical and topological foundations.

**This is an incomplete, evolving formalization.** Definitions and proved
conditional results are available for reuse; several major comparison and
localization theorems remain open. Read [the mathematical scope](docs/STATUS.md)
before using a theorem family.

## Use as a dependency

Use Lean **4.34.0** and add this to your `lakefile.toml`:

```toml
[[require]]
name = "quillen-k-theory"
git = "https://github.com/kangxyz/quillen-k-theory.git"
rev = "v0.1.0"
```

Then choose the smallest import you need:

```lean
import Quillen.CategoryTheory.ExactCategory.Basic
import Quillen.KTheory.API
```

The existing public entrypoints remain available:

```lean
import Quillen.Library     -- public K/G interfaces and their foundations
import Quillen.Scheme      -- geometric K/G interfaces
import Quillen.Resolution  -- finite-resolution comparisons
```

`import Quillen` loads the complete library. Generated family entrypoints such
as `Quillen.Topology`, `Quillen.KTheory`, and `Quillen.Waldhausen` are available
when you want a whole mathematical topic. Prefer individual modules for lighter
imports. See [the library guide](docs/LIBRARY.md) for namespaces, hypotheses,
universe conventions, and working client proofs.

## Build and check

Install [elan](https://github.com/leanprover/elan), then run:

```sh
bash scripts/cache.sh
lake build
bash scripts/audit.sh --rehash
```

Lean, mathlib, and all transitive dependencies are pinned. The audit checks
layout, source placeholders, the complete library's axiom dependencies, and a
separate downstream Lake package. It permits only `propext`, `Classical.choice`,
and `Quot.sound`. Build products and dependencies stay outside Git.

The cache script fetches only mathlib modules required by this library and its
checked client, including their transitive imports.

## Organization and development

```text
Quillen/              reusable mathematics, grouped by mathematical objects
Quillen.lean          generated complete import entrypoint
audits/               executable trust checks and retained regression probes
examples/downstream/  separate package using the public library
docs/                 API, scope, architecture, and mathematical notes
scripts/              import generation and structural checks
```

The structure is open to new subjects and modules. Adding a theorem does not
require updating a fixed source inventory or a historical proof hash. Run
`python3 scripts/generate_imports.py` to update import entrypoints, then build
and audit. Implementation modules import their precise dependencies; library
code does not import audits or clients.

[CONTRIBUTING.md](CONTRIBUTING.md) describes adding modules, evolving the API,
and updating dependencies. [ARCHITECTURE.md](docs/ARCHITECTURE.md) explains the
dependency boundaries. Version `0.x` APIs may change; consumers should pin a
release tag or commit. The existing declaration names are preserved in this
initial extraction.

## Provenance and license

The initial source comes from the supplied 2026-10-09 14:55 UTC checkpoint.
All existing mathematical implementation files are preserved. Research logs,
build caches, and the checkpoint's immutable packaging machinery are excluded
from the repository. See [PROVENANCE.md](docs/PROVENANCE.md) and
[the initial release record](docs/RELEASE.md).

Released under [Apache-2.0](LICENSE).

Mathematical references include
[Quillen, Higher Algebraic K-theory I](https://link.springer.com/chapter/10.1007/BFb0067053)
and [Bühler, Exact Categories](https://arxiv.org/abs/0811.1480).
The organization follows relevant
[mathlib style and documentation conventions](https://leanprover-community.github.io/contribute/style.html).
