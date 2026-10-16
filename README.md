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
`BGL(R)⁺` model and a homotopy equivalence with exactly the standard map to the
zero component of original Q loops. The whole original Q-loop space is homotopy
equivalent to discrete original K₀ times this specific plus model. Positive
K-group comparisons are natural under ring change, and the product-to-loop map
has ordinary homotopy naturality. Literal noncommutative balanced tensors
identify with the original finite-projective scalar extension through its Hom
universal property. See [the ring plus guide](docs/topics/PlusConstruction.md)
for the coefficient universes, prescribed basepoint tracks and comparison boundaries.

For original plus maps on actual Hausdorff CW spaces, it constructs comparison
homotopy equivalences and proves ordinary uniqueness. Covers, lifts and double
cylinders are constructed; mixed universes retain an explicit common
coefficient bound. See [classical CW plus comparisons](docs/topics/ClassicalCWPlus.md)
and [homotopy foundations](docs/topics/HomotopyFoundations.md).

The actual two-chart projective line also has finite-projective Čech models
for vector bundles, objectwise global strict models of arbitrary intrinsic
perfect objects in the bounded-below derived category, and perfect images
under its original derived projection over every commutative ring, including
the zero ring. Natural intrinsic-perfect diagonal generation and both
original affine K-map inverse laws are proved. On qcqs bases both actual
native model inverse laws are proved, and the geometric coefficient pair
is identified with the inverse of the existing two-summand native K-map.
The original inverse-image supported map is bijective for compact base
opens, including degree zero. The general projective-bundle formula and
classical nonconnective identification remain separate. For quasi-compact opens of affine schemes,
full-open graded coefficient diagrams have natural Bass seed nullhomotopies
and vanishing signed stable groups of their actual graded telescopes.
The original coarse-to-fine section telescope restriction is stable in every
integer degree, and the supported telescope gives constructed affine full-open
section-completion localization with its original signed boundary.
Native global coefficient Models also have the same original coarse-to-fine
completion comparison and supported localization in every integer degree,
including the actual auxiliary-supported fiber and original signed boundary,
under their stated compactness and quasi-separatedness conditions. Completed
geometric evaluation, raw all-iterate and telescope comparisons, and classical
nonconnective identification remain separate; the
[perfect-complex guide](docs/topics/PerfectComplexes.md) records their scope.

The project is under development. The [documentation map](docs/README.md)
connects its mathematical topic guides, [coverage and open boundaries](docs/reference/Scope.md),
and [public API reference](docs/reference/API.md).

## Quick start

The **0.9.0 candidate-organization version** uses Lean **4.34.1** and the mathlib revision
pinned in [lakefile.toml](lakefile.toml). General algebra, exact categories,
scheme modules and cohomology use accepted implementations from
[Aglib](https://github.com/kangxyz/aglib), pinned to
`40af743ab794d607f566cec0c5417d8e4d02a735`. Quillen imports its precise modules
and native mathematical namespaces, and owns the Q/K/G constructions and
application maps. Further general implementations awaiting upstream admission
live in the [local Aglib candidate tree](Quillen/Aglib/README.md), separated from
their specialized applications with one local implementation per declaration.
Install
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

Version 0.7.0 integrates the classical CW and homotopy foundations and directly
normalizes the public plus/Q comparison to the standard sign; see
[standard comparison normalization](docs/reference/StandardSignMigration.md).
The earlier 0.5.0 generic-owner refactor is preserved; its
[migration notes](docs/reference/API.md#migration-to-050) locate the current
foundations and remove obsolete imports and duplicate API spellings.

Import the interface you need:

```lean
module

import Aglib.CategoryTheory.ExactCategory.Functor
import Quillen.KTheory.API

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Quillen

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
`Quillen.Aglib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal`.
`import Quillen` imports the complete library. See the
[module-path conventions](docs/reference/API.md#module-paths-and-namespaces) when
choosing focused imports.

## Native build cache

The package enables Lean 4.34.1 Lake's native artifact cache and restores
conventional `.lake/build` files for audits. Checkouts keep separate writable
build directories while Lake shares immutable artifacts and native input
mappings. Mathlib retains `lake exe cache get` through the existing cache route.

CI uses the canonical [Aglib cache protocol](https://github.com/kangxyz/aglib/blob/main/doc/CACHING.md)
from a separately pinned tooling checkout, without changing mathematical pins.
It restores native partial progress across manifest/pin changes and imports
public upstream cache release assets. Exact-pin assets are preferred; bounded
recent compatible producer assets can seed unchanged leaves. Producer revisions
remain explicit and ordinary `--rehash` builds decide actual input applicability.
After successful main checks, a separate publish job creates a public native
cache prerelease for downstream consumers. Existing checkout caches and all
normal checks remain in place. Legacy configuration keys exclude only top-level
package `version`, `enableArtifactCache` and `restoreAllArtifacts`, preserving
pre-migration conventional outputs. Compiler options, pins and toolchains remain
significant, and normal Lake input validation still applies.

For local upstream reuse, set `AGLIB_CACHE_TOOLING` to a reviewed Aglib tooling
checkout and run before the selected leaf's normal rehashed build:

```sh
python3 "$AGLIB_CACHE_TOOLING/.github/actions/lake-cache/cache.py" --root . restore \
  --repositories kangxyz/aglib
```

No dependency update or cross-repository credential is required. An unavailable
or incompatible cache falls back to normal compilation. Cache hits do not
replace current checks or establish new verification evidence.

## Documentation

Use the [documentation map](docs/README.md) to choose a mathematical topic or
shared reference. It connects the topic guides to API, scope, architecture,
and performance documentation. [Contributing](CONTRIBUTING.md)
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
