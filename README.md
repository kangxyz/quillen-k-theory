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
against arbitrary target modules. See [the ring plus guide](docs/topics/PlusConstruction.md)
for the exact coefficient universes, basepoint paths, and remaining comparisons.

The actual two-chart projective line also has finite-projective Čech models
and perfect derived projection images for vector bundles and explicitly
bounded complexes of vector bundles. For quasi-compact opens of affine schemes,
full-open graded coefficient diagrams have natural Bass seed nullhomotopies
and vanishing signed stable groups of their actual graded telescopes.
The original coarse-to-fine section telescope restriction is stable in every
integer degree, and the supported telescope gives constructed affine full-open
section-completion localization with its original signed boundary.
Native global coefficient Models also have the same original coarse-to-fine
completion comparison in every integer degree. Basic global supported
localization and the auxiliary-supported coarse-to-fine completion comparison
are also proved. Auxiliary-supported fiber localization, completed geometric
evaluation and classical nonconnective identification remain separate
comparisons; the [perfect-complex guide](docs/topics/PerfectComplexes.md)
records their scope.

The project is under development. The [documentation map](docs/README.md)
connects its mathematical topic guides, [coverage and open boundaries](docs/reference/Scope.md),
and [public API reference](docs/reference/API.md).

## Quick start

The **0.5.0 development version** uses Lean **4.34.1** and the mathlib revision
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

Version 0.5.0 consolidates shared foundations and moves generic algebra out of
geometric and G-theory application owners. It removes obsolete imports and
duplicate API spellings; see the [migration notes](docs/reference/API.md#migration-to-050).

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
[module-path conventions](docs/reference/API.md#module-paths-and-namespaces) when
choosing focused imports.

## Documentation

Use the [documentation map](docs/README.md) to choose a mathematical topic or
shared reference. It separates the seven topic guides from API, scope,
architecture, and performance documentation. [Contributing](CONTRIBUTING.md)
gives the source and checking workflow.

## Building and checking

From the library checkout, run:

```sh
bash scripts/cache.sh
bash scripts/check.sh --rehash
```

The cache script selects required mathlib imports. The check script validates
source structure, builds the library and tests, runs lint, builds the downstream
package, and replays the transitive axiom audits. See
[verification scope](docs/reference/Scope.md#verification) for what these checks cover.

## License

[Apache-2.0](LICENSE).
