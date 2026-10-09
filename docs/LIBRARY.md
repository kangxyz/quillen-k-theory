# Using Quillen as a Lean library

Lean and mathlib are pinned by `lean-toolchain`, `lakefile.toml`, and the committed
manifest. All implementation files live in thematic directories. Historical
flat implementation aliases have been removed; clients should use current
canonical imports. Existing mathematical modules are unchanged in the initial
standalone extraction. The complete root and optional subject entrypoints are
generated from the evolving source tree. See [LIBRARY_LAYOUT.md](LIBRARY_LAYOUT.md)
and [CONTRIBUTING.md](../CONTRIBUTING.md) for extension and compatibility rules.

## Add a released dependency

Use the same Lean toolchain and add this to another Lake package:

```toml
[[require]]
name = "quillen-k-theory"
git = "https://github.com/kangxyz/quillen-k-theory.git"
rev = "v0.1.0"
```

Pin a release tag or exact commit. During version `0.x`, future minor releases
may change APIs, hypotheses, or import paths, with explicit migration notes.

## Add a local dependency

In another Lake package, use:

```toml
[[require]]
name = "quillen-k-theory"
path = "../quillen-k-theory"
```

Use the same Lean toolchain. `examples/downstream` is a separate Lake package
with this path dependency and its own manifest and build directory. It compiles
ordinary client proofs, rather than checking names inside the source package.

## Choose an import

```lean
import Quillen.Library
```

This curated entrypoint provides the exact-category, dévissage, Serre localization,
finite-module G-theory, and geometric scheme interfaces. For focused imports:

- `Quillen.KTheory.API`: exact K-groups, exact-functor maps, equivalences, bundled
  group-valued functors, and small models
- `Quillen.Devissage.Homotopical`: finite-filtration dévissage and its canonical map
- `Quillen.Localization.Serre.LocalizationTheorem`: canonical connective Serre LES
- `Quillen.Localization.Serre.LocalizationTarget`: comparison with an actual exact
  quotient functor
- `Quillen.GTheory.FiniteModules.LocalizationSequence`: finite-module G-localization
- `Quillen.Scheme`: actual vector-bundle K-theory, coherent G-theory and open restriction
- `Quillen.Scheme.AffineGTheory`: lower-universe affine G-theory and principal-open LES
- `Quillen.Scheme.PrincipalGTheory`: principal-open LES directly on public global G/SupportedG
- `Quillen.Scheme.AffineClosedGTheory`: arbitrary-ideal affine closed dévissage
- `Quillen.Scheme.Regular`: canonical K→G for all regular affines and quasi-compact
  regular schemes with the ordinary resolution property
- `Quillen.Topology.Realization.EdgewiseRealization`: genuine edgewise realization
  homotopy equivalence with canonical endpoint and chosen-vertex formula
- `Quillen.Resolution`: full objectwise finite all-degree resolution comparison
- `Quillen.Scheme.ClosedGTheory`: arbitrary noetherian closed-subscheme dévissage
- `Quillen.PerfectComplexes.Basic`: strict/local perfect connective K and actual
  restriction/support/comparison maps; see the exact comparison scope below

`import Quillen` remains the full checked integration entrypoint. Implementation
imports below the thematic directories are available for finer-grained use.
There is no compatibility entrypoint. `module-migration.json` records removed
paths and their canonical replacements for updating older consumers.

## Stable mathematical namespaces

The source move preserves all existing declarations and their namespaces:

- `Quillen.ExactStructure`: `E.QCategory`, `E.KSpace`, `E.kBasepoint`, `E.K n`,
  `E.SmallK n`
- `Quillen.ExactFunctor`: `F.mapQ`, `F.KMap n`, `F.smallKMap n`, `KMap_id`,
  `KMap_comp`, `KMap_eq_of_natIso`, canonical exact-equivalence maps,
  `smallKMap_id`, `smallKMap_comp`, and `smallKMap_eq_of_natIso`
- `Quillen.SmallExactCategory`: `ofExactStructure E`, `KFunctor n`
- `Quillen.Devissage`: `FiltrationHypothesis P`, `KEquiv P h n`, `KMap P n`
- `Quillen.SerreLocalization`: `quotientKMap P n`, `connectingHom P n`,
  `localizationSequence P`, and all three exactness positions
- `Quillen.FiniteModuleLocalization`: `G R n`, `SupportedG S n`,
  `localizationKMap S n`, `supportedKMap S n`, and `connectingHom S n`

Existing mathematical declaration names are preserved; import paths must be updated. The public API adds constructors
and computation lemmas without substituting a different K-map. For example:

```lean
import Quillen.KTheory.API

open CategoryTheory CategoryTheory.Limits Quillen

example {C D T : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} T]
    [Preadditive C] [HasFiniteBiproducts C]
    [Preadditive D] [HasFiniteBiproducts D]
    [Preadditive T] [HasFiniteBiproducts T]
    {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure T}
    (F : ExactFunctor E E') (G : ExactFunctor E' E'') (n : ℕ) (x : E.K n) :
    (F.comp G).KMap n x = G.KMap n (F.KMap n x) := by
  simp
```

See the compiled `Consumer/` files for canonical-map comparisons, dévissage,
all three Serre exactness positions, actual finite-module localization (including
`ℤ → ℤ[1/2]`), scheme restriction, and small-model identity/composition/natural-iso laws.

## Scheme API and universe boundaries

`Quillen.Scheme.K X n` uses finite locally free sheaves on any scheme.
`Quillen.Scheme.G X n` uses actual coherent sheaves on a locally noetherian scheme.
For `X : AlgebraicGeometry.Scheme.{u}`, both types live in `Type (u + 1)`.
`Quillen.Scheme.restrictK j n` and `restrictG j n` are the canonical maps of actual
geometric open restriction. Their `_eq_smallKMap` lemmas identify the exact functor
used. The generic chosen-small-model construction now has proved identity, composition,
and natural-isomorphism-invariance laws for exact functors. The open-immersion interface packages the actual restriction laws as
`KOpenFunctor`, `GOpenFunctor` and `KToGOpenNatTrans`. No pullback functor
on arbitrary scheme morphisms is asserted.

The established affine presentation is separately named
`Quillen.Scheme.Affine.G R n : Type u`. `moduleEquiv` gives its canonical finite-module
comparison. `restrictG`, `inclusionG`, and `boundaryG` give the actual principal-open
sequence, with a theorem at each exactness position and the surjective G₀ endpoint.
The actual global-to-affine coherent-category equivalence is available as
`Quillen.CoherentScheme.coherentAffineEquivalence R`; finite-presentation and
affine comparison proofs live in their own thematic files. The library does not
identify these lower-universe groups with global
`Quillen.Scheme.G (Spec R) n` merely by abbreviation. `SupportedG` for a general open
is a genuine support group. `Quillen.Scheme.Localization` supplies its actual
connective localization sequence for arbitrary open immersions into noetherian schemes.

## Implementation layers

| Directory | Responsibility |
| --- | --- |
| `CategoryTheory/ExactCategory` | Exact structures, functors, quotients and conflations |
| `CategoryTheory/QConstruction` | Restricted spans and genuine Q-composition |
| `CategoryTheory/SmallModel` | Exact/abelian transport to categorical small models |
| `CategoryTheory/TheoremA`, `TheoremB` | Categorical fiber and equivalence theorems |
| `Topology/ClassifyingSpace` | Nerves, realization, maps, and basepoints |
| `Topology/Realization` | Simplicial realization and edge-path presentation |
| `Topology/HomotopyFiber`, `HomotopyGroups` | Actual path-space fibers and LES |
| `Topology/HELP`, `HomotopyEquiv`, `FilteredRealization` | Homotopy-invariance infrastructure |
| `KTheory` | Genuine K-groups, maps, functors and K₀ comparison work |
| `Devissage` | Filtrations, layers, canonical inclusion and dévissage |
| `Localization/Serre` | Serre quotient comparison and connective K-localization |
| `GTheory/FiniteModules` | Finite-module foundations and scalar localization |
| `Scheme/Sheaf` | Ambient sheaf exactness and geometric support |
| `Scheme/Coherent` | Global and affine coherent sheaf categories and G-theory |
| `Scheme/VectorBundle` | Finite locally free sheaves, exactness and K-theory |
| `Scheme/Regular`, `Scheme/Comparison` | Geometric comparison and regular affine cases |
| `Resolution` | Exact-category admissible resolution comparisons |
| `PerfectComplexes`, `Waldhausen` | Actual strict/local perfect connective S-theory; comparisons remain ongoing |

Module layout is separate from mathematical namespace: foundational declarations
keep their natural `Quillen.ExactStructure`, `Quillen.TheoremA`, and similar names.

## Validation and source integrity

Run:

```sh
lake build
bash scripts/audit.sh --rehash
```

`check_library_layout.py` enforces resolved imports, acyclic dependencies, source
enrollment, generated-entry consistency, and library/client separation. It
rejects obsolete implementation aliases and loose root audit/proof files.
`check_placeholders.py` recursively scans the complete thematic source tree.
`audits/LibraryAudit.lean` checks declaration dependencies by project module origin, including
private declarations, permitting only Lean's standard logical foundations.
`check_library.sh` builds the full canonical integration entrypoint, public
umbrellas and the independent consumer package, then audits the consumer declarations too.

The machine-readable migration map is historical reference for old paths and
their replacements. Its proof fingerprints do not freeze future development.
Every present source module is enrolled in the generated complete library;
unaccepted experiments belong outside the production source tree.

See `STATUS.md` for mathematical boundaries. In particular, K₀ presentation
comparison, regular K=G without the stated resolution-property hypothesis,
and the remaining perfect-complex comparison/localization theorems must not
be inferred from an import path or an API abbreviation. Arbitrary noetherian
closed-subscheme G-dévissage is a proved endpoint.

The public global principal-open API is `Quillen.Scheme.Principal.inclusionG`, `boundaryG`, the three range/kernel lemmas, and `restrictG_zero_surjective`. Its open map is exactly `Quillen.Scheme.restrictG`. The separately named affine API retains its lower-universe scope.

### General noetherian open and closed interfaces

`Quillen.Scheme.Localization` exposes `Scheme.inclusionG`, `boundaryG`, `localization_longExact`, three individual range/kernel lemmas and `restrictG_zero_surjective` for arbitrary open immersions into noetherian schemes. `Quillen.Scheme.ClosedGTheory` exposes actual arbitrary closed pushforward, dévissage and the canonical geometric closed/open sequence. The principal and affine-closed files retain their specialized formulas. `Quillen.Scheme.Comparison.KToG` exposes the canonical exact inclusion map and its restriction naturality. `Quillen.Scheme.OpenImmersionFunctor` packages the restriction laws as `KOpenFunctor`, `GOpenFunctor` and `KToGOpenNatTrans`. All are imported by `Quillen.Scheme`. The independent consumer includes proofs using these interfaces.

### Affine closed and PID comparison interfaces

`Quillen.Scheme.AffineClosedGTheory` exposes the arbitrary-ideal affine closed
comparison and the canonical pushforward identification for a noetherian
commutative ring. `Quillen.Scheme.Regular` exposes `Scheme.KToGPIDEquiv R n`,
`KToG_pid_bijective`, and its exact forward-map identity with `Scheme.KToG`.
These are specific proved affine endpoints, not a claim of unrestricted global
regular K=G. The independent consumer includes `Consumer.AffineClosed`,
`Consumer.Resolution`, and `Consumer.Regular`.

### Canonical regular comparison

`import Quillen.Scheme.Regular` exposes `Scheme.KToGRegularAffineEquiv` for
all regular affine rings, without a finite Krull-dimension bound, and the
nonaffine endpoint below. The earlier PID and dimension-one APIs remain
specialized proved formulas. `Consumer/Regular.lean` checks the canonical
map and agreement of the affine and global equivalences.

## Current regular and locally-perfect interfaces

The public nonaffine regular theorem is:

```lean
example (X : AlgebraicGeometry.Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ) :
    (Quillen.Scheme.KToGRegularEquiv X n).toMonoidHom =
      Quillen.Scheme.KToG X n := rfl
```

`IsRegular` is the actual stalk condition. `HasResolutionProperty` is the
ordinary one-step vector-bundle quotient condition. Finite resolution is a
proved conclusion. The equivalence agrees with `KToGRegularAffineEquiv` on Spec.

For any scheme X, `Quillen.PerfectComplexes.PerfectK X n` is genuine
locally-perfect S-theory. `perfectKRestrict`, `strictToPerfectKMap`,
`PerfectSupportedK`, and `perfectSupportedKMap` provide the actual maps.
The source of `vectorBundleToPerfectSMap` is vector-bundle S-theory. The
proved canonical Q/S equivalence now identifies exact-category S-theory with
Q-theory; the public geometric bridge is described below.


### Public small model and actual vector bundles

`Quillen.Scheme.Comparison.SmallVectorBundleK` exposes
`SchemeSheaf.smallVectorBundleKEquiv X n`. It identifies public `Scheme.K`
with the actual vector-bundle Q-model. Their Q-realizations already inhabit
the common universe `u+1`; no arbitrary cross-universe realization theorem
is used. The forward homomorphism is exactly `smallVectorBundleKMap`.
The proved Q/S equivalence can be composed with this bridge;
Gillet–Waldhausen remains separate.

### Change of perfect-complex cofibrations

`Quillen.PerfectComplexes.SplitComparison` (also in `PerfectComplexes.Basic`)
exposes `splitStrictKEquiv X n` and `splitPerfectKEquiv X n` for every scheme
and every nonnegative degree. Their forward maps are the existing canonical
`splitStrictToStrictKMap` and `splitPerfectToPerfectKMap`, with definitional
`_toMonoidHom` lemmas. This compares globally degreewise-split and ambient-mono
cofibrations with perfect quotient on the same actual object categories.
It does not identify strict objects with all locally-perfect objects.

### Canonical exact-category Q/S comparison

`Quillen.Waldhausen.QuillenComparison.Equivalence` exposes
`Waldhausen.QuillenComparison.comparisonKEquiv E n` from the original
exact-category S-groups to `E.K n`, with underlying map exactly `comparisonK`.
The realized subdivision comparison is an actual homotopy equivalence with
its prescribed forward map and chosen zero point. The companion
`Functoriality` module proves strict naturality of the raw simplicial map.
Both modules are included in `Quillen.Library`.

### Public scheme K to perfect-complex K

`Quillen.PerfectComplexes.QuillenComparison` is included in `PerfectComplexes.Basic`.
`vectorBundleQSEquiv X n` identifies public scheme K with exact vector-bundle
S-theory. The actual `vectorBundleToStrictKMap` and
`vectorBundleToPerfectKMap` then land in strict and locally-perfect K.
`strictToPerfect_comp_vectorBundleToStrictKMap` proves the expected factorization.
No equivalence of either perfect-complex target with vector-bundle K is claimed
until Gillet–Waldhausen and the relevant geometric comparison are proved.
