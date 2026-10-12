# Quillen K-theory

[![CI](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml/badge.svg)](https://github.com/kangxyz/quillen-k-theory/actions/workflows/ci.yml)

A Lean library for algebraic K-theory and its algebraic, categorical, geometric,
and homotopical foundations, built on mathlib.

The library develops exact categories, Quillen's Q-construction, Waldhausen's
S-construction, scheme K/G-theory, and perfect complexes. It includes canonical
maps, comparison theorems, connective localization and Mayer–Vietoris sequences,
an iterated S-construction Ω-spectrum, and functorial Bass negative groups
defined by cokernel recursion. Perfect spectra admit derived pullback in the
constructed stable localization. The source is organized for reuse and extension
to further constructions and comparisons.

For arbitrary unital rings, it also constructs an independent homological
`BGL(R)⁺` model, a specified weak equivalence to the zero component of original
Q loops, and positive K-group comparison maps natural under ring change.
Finite-projective ring change has the scalar-extension Hom universal property
against arbitrary target modules. See [the ring plus guide](docs/PlusConstruction.md)
for the exact coefficient universes, basepoint paths, and remaining comparisons.

The project is under development. [Mathematical scope](docs/Scope.md) records
precise coverage and open boundaries; the [library guide](docs/Library.md)
provides imports and public interfaces.

## Quick start

The **0.4.1 development version** uses Lean **4.34.1** and the mathlib revision
pinned in [lakefile.toml](lakefile.toml). Install
[elan](https://github.com/leanprover/elan) to use the committed
[toolchain](lean-toolchain).

For a local checkout beside your Lean project, add this to `lakefile.toml`:

```toml
[[require]]
name = "quillen-k-theory"
path = "../quillen-k-theory"
```

Run `lake update quillen-k-theory`, then `lake build` in your project.
For a published dependency, replace `path` with
`git = "https://github.com/kangxyz/quillen-k-theory.git"` and a `rev` pinned to
the selected release tag or commit. The candidate version does not itself
identify a published tag.

Import the interface you need:

```lean
module

import Quillen.KTheory.API

universe u
open CategoryTheory CategoryTheory.Limits Quillen

example {C : Type u} [Category.{u} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) (n : ℕ) (x : E.K n) :
    (ExactFunctor.id E).KMap n x = x := by
  simp
```

Exact functors induce the displayed maps on K-groups. More client proofs are in
the [separate downstream package](examples/downstream/Consumer).

For geometric interfaces, use `Quillen.AlgebraicGeometry.Scheme`; for a focused
perfect-localization import, use
`Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization`.
For ring plus comparison, use `Quillen.KTheory.Plus`; for the scalar-extension
universal property, use
`Quillen.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal`.
`import Quillen` imports the complete library. See the
[module-path conventions](docs/Library.md#module-paths-and-namespaces) when
choosing focused imports.

## Documentation

- [Library guide](docs/Library.md): imports, canonical maps, spectra, Bass groups, and universes.
- [Mathematical scope](docs/Scope.md): result families, hypotheses, and open comparisons.
- [Perfect-complex localization](docs/ThomasonTrobaugh.md): relative models, support excision, Mayer–Vietoris, and degree zero.
- [Ring plus construction](docs/PlusConstruction.md): the independent model, original Q comparison, components, and scalar extension.
- [Architecture](docs/Architecture.md): mathematical owners and dependency boundaries.
- [Typechecking performance](docs/Performance.md): measured costs and a verified instance-inference optimization.
- [Contributing](CONTRIBUTING.md): extending the library and checking changes.

## Building and checking

From the library checkout, run:

```sh
bash scripts/cache.sh
bash scripts/check.sh --rehash
```

The cache script selects required mathlib imports. The check script validates
source structure, builds the library and tests, runs lint, builds the downstream
package, and replays the transitive axiom audits. See
[verification scope](docs/Scope.md#verification) for what these checks cover.

## License

[Apache-2.0](LICENSE).
