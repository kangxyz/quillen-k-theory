# Library architecture

The reusable source graph is rooted at `Quillen/`. Directories are mathematical
owners rather than stages of one paper or a fixed project roadmap. New subject
directories can be added when there is actual source to place there.

## Dependency boundaries

| Source | Role | Dependency boundary |
| --- | --- | --- |
| `Quillen/<Subject>/**/*.lean` | Definitions and proofs | Precise mathlib and Quillen implementation modules |
| `Quillen.lean` | Complete generated import surface | All current Quillen source modules |
| Generated `Quillen/<Subject>.lean` | Optional whole-topic import | Modules under that subject directory |
| `Quillen.Library`, `Quillen.Scheme`, `Quillen.Resolution` | Selected public entrypoints | Hand-selected canonical library modules |
| `audits/` | Trust checks and regression probes | Library modules; never imported by library code |
| `examples/downstream/` | Independent client package | Published library through a Lake dependency |

Object-level foundations support comparison theorems and applications. Some
categorical homotopy theorems need topology, and some topological constructions
need category theory. The checker enforces a directed acyclic module graph,
rather than an artificial total order on subject names.

Implementation modules should avoid whole-library and whole-family imports.
Such imports pull unrelated code into consumers and can create a cycle when a
new module joins the family. Import the exact foundational module instead.

## Import generation and source enrollment

`scripts/generate_imports.py` scans the source tree and emits deterministic
alphabetical imports. Run it after adding, moving, or removing source modules.
The `--check` mode reports stale generated files without changing them. The
layout checker detects unresolved imports, cycles, unenrolled source modules,
obsolete implementation paths, and imports of clients/audits from library code.

The manually selected public entrypoints are not overwritten by generation.
They can retain a useful smaller dependency boundary even as the complete
library grows. Each new source module enters the complete build and transitive
axiom audit; no source-count registry or initial proof fingerprint needs editing.

## Current mathematical families

The present source covers algebraic foundations, exact categories and
Q-constructions, categorical Theorems A/B, topology and homotopy, K-theory,
dévissage, Serre localization, finite-module G-theory, schemes, resolution,
perfect complexes, and Waldhausen constructions.

These are current consumers, not an exhaustive taxonomy. Add further algebraic,
geometric, categorical, or homotopical developments at their natural owners.
Split a growing module when that creates a useful independent import boundary;
keep downstream comparison modules dependent on those foundations.

## Trust and evidence

The root build enrolls all library source. `audits/LibraryAudit.lean` traverses
declarations by their originating project modules, including private and
generated helpers, and checks transitive axiom dependencies. The downstream
package has a separate declaration audit. Both admit only the standard Lean
logical foundations `propext`, `Classical.choice`, and `Quot.sound`.

The supplied checkpoint's review and mathematical notes remain source material
for understanding hypotheses and unfinished work. Their historical check
results do not replace checks of the current source. The current release
records its own results, and ordinary development is checked by CI.

No experiment, cache, raw build log, or downstream client is a dependency of
the reusable mathematics. See [CONTRIBUTING.md](../CONTRIBUTING.md) for extension,
compatibility, and release procedures.
