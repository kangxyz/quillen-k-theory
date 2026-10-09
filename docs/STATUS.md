# Mathematical scope

This library formalizes part of connective algebraic K-theory. It does not
claim a complete formalization of Quillen's theory or a spectrum-level,
nonconnective theory. The initial packaging preserves the supplied checkpoint's
mathematical source and hypotheses.

## Implemented theorem families

| Family | Import starting point | Scope to retain when using it |
| --- | --- | --- |
| Exact structures and Q-construction | `Quillen.CategoryTheory.ExactCategory.Basic`, `Quillen.CategoryTheory.QConstruction.Basic` | Genuine restricted spans and exact-category structure |
| K-groups and functorial maps | `Quillen.KTheory.API` | Actual based homotopy groups, exact-functor maps, small-model conventions |
| Homotopical dévissage | `Quillen.Devissage.Homotopical` | The stated abelian and filtration hypotheses |
| Connective Serre localization | `Quillen.Localization.Serre.LocalizationTheorem` | The actual quotient and canonical maps; connective K₀ tail |
| Scheme K/G interfaces | `Quillen.Scheme` | Actual vector bundles/coherent sheaves and explicit universe conventions |
| Closed-support G-theory | `Quillen.Scheme.ClosedGTheory`, `Quillen.Scheme.Localization` | The stated noetherian hypotheses and actual open/closed maps |
| Finite-resolution comparison | `Quillen.Resolution` | Admissible objectwise finite resolutions |
| Regular K→G comparison | `Quillen.Scheme.Regular` | Regular affine schemes; quasi-compact regular schemes with the resolution property |
| Exact-category Q/S comparison | `Quillen.Waldhausen.QuillenComparison.Equivalence` | Canonical maps for the stated exact categories |
| Perfect-complex foundations | `Quillen.PerfectComplexes.Basic` | Strict and locally-perfect connective models, actual quasi-isomorphisms, stated cofibrations |
| Additivity and finite filtration comparisons | `Quillen.Waldhausen`, `Quillen.KTheory` | The actual objects, maps, and hypotheses in individual declarations |
| Finite HELP and compact lifting infrastructure | `Quillen.Topology.HELP.FiniteCharacterization` | Finite cubes and the explicitly stated compact-test lifting conditions |

The [library guide](LIBRARY.md) gives qualified names, universe boundaries, and
client examples. The [historical checkpoint report](history/STATUS_20261009_1455.md)
retains the detailed prior verification and review claims. Use the present Lean
statements for exact premises; this table is an index, not a replacement for them.

## Open theorem families

- Gillet–Waldhausen, strict versus locally-perfect comparison, and perfect
  localization.
- Global change-of-weak-equivalences fibration and the remaining finite
  weak-cartesian gluing step.
- Identification of homotopical K₀ with the algebraic Grothendieck presentation.
- General exact-category dévissage/localization beyond the implemented abelian
  and resolving-subcategory statements.
- Full Serre-pair functorial naturality with quotient and basepoint coherence.
- Cross-universe raw realization comparison and arbitrary chosen-model transport.
- Plus-construction comparison, spectra, nonconnective tails, and numerical
  computations.

Regularity alone does not supply the resolution property on an arbitrary
scheme. Finite cube HELP is not an arbitrary compact HELP theorem, and endpoint
collar deformation alone does not provide vertical lifting. Keep these
boundaries when combining the available results.

## Verification

The initial release checks are recorded in [RELEASE.md](RELEASE.md). Builds
check Lean terms and the complete source import graph; axiom audits check their
transitive foundation dependencies. They do not independently review the
translation of every mathematical statement. The scope remains partial when
all checks pass.
