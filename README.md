# Quillen K-theory

[![CI](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml)

A Lean library for Quillen K-theory and related mathematics, built on mathlib.

The library includes exact categories, Quillen's Q-construction, Waldhausen's
S-construction, and geometric K/G-theory, together with their algebraic,
categorical, and homotopical foundations. Its current models are connective;
the project is open to further constructions and comparisons.

The project is under development. See [mathematical scope](docs/Scope.md) for
the hypotheses of the available results and the remaining comparison theorems.

## Installation

Use Lean **4.34.0** and add the following dependency to `lakefile.toml`:

```toml
[[require]]
name = "quillen-k-theory"
git = "https://github.com/kangxyz/quillen-k-theory.git"
rev = "v0.1.0"
```

Resolve the new dependency with `lake update quillen-k-theory`, then build your
package with `lake build`.

Import individual modules for a small dependency footprint:

```lean
import Quillen.CategoryTheory.ExactCategory.Basic
import Quillen.KTheory.API
```

`Quillen.Library` collects the public K/G interfaces; `Quillen.Scheme` and
`Quillen.Resolution` provide the geometric and finite-resolution interfaces.
`import Quillen` imports the entire library.

## Example

In the exact-category interface, exact functors induce maps on K-groups:

```lean
import Quillen.KTheory.API

universe u
open CategoryTheory CategoryTheory.Limits Quillen

example {C : Type u} [Category.{u} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) (n : ℕ) (x : E.K n) :
    (ExactFunctor.id E).KMap n x = x := by
  simp
```

The [downstream examples](examples/downstream/Consumer) exercise the public API
from a separate Lake package.

## Documentation

- [Library guide](docs/Library.md): imports, namespaces, maps, and universe conventions.
- [Mathematical scope](docs/Scope.md): theorem families and open problems.
- [Architecture](docs/Architecture.md): module organization and dependency boundaries.
- [Contributing](CONTRIBUTING.md): extending the library and checking changes.

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```sh
bash scripts/cache.sh
bash scripts/check.sh --rehash
```

The toolchain and dependencies are pinned. The checks build the library and its
downstream examples, and audit transitive axiom dependencies.

## License

[Apache-2.0](LICENSE).
