# Mathematical scope

The library develops algebraic K-theory through several constructions, including
Quillen's Q-construction and Waldhausen's S-construction. The present models are
connective, and the formalization is incomplete. The Lean statements specify
the objects, hypotheses, and comparisons of each result.

## Available interfaces and results

| Family | Scope |
| --- | --- |
| Exact categories and Q-construction | Exact structures, restricted spans, composition, and compatible functors |
| K-groups and canonical maps | Based homotopy groups, exact-functor laws, equivalences, and chosen small-model interfaces |
| Dévissage | The stated abelian finite-filtration setting |
| Serre localization | Connective localization for the specified Serre quotient, including the K₀ tail |
| Scheme K/G-theory | Vector bundles, coherent sheaves, open restriction, and canonical K→G maps |
| Closed-support G-theory | Noetherian open/closed localization and closed-subscheme dévissage |
| Resolution | Admissible objectwise finite-resolution comparisons |
| Regular K→G | Regular affines; quasi-compact regular schemes with the resolution property |
| Q/S comparison | Canonical exact-category Quillen/Waldhausen comparison |
| Perfect-complex models | Strict/local connective models, genuine derived local perfectness, restriction, support, and change-of-cofibration comparisons |
| Gillet–Waldhausen | Bounded-complex comparison under the stated term-property hypotheses; vector-bundle/strict-perfect equivalence on every scheme |
| Affine perfect comparisons | Strict/local and vector-bundle/local equivalences in every nonnegative degree |
| Relative and supported affine comparisons | Strict/local comparisons for any open immersion into `Spec R`; no quasi-compactness of the open is required |
| Principal perfect localization | Connective group exactness for `Spec R[r⁻¹] → Spec R` over every commutative ring |
| Pullback | Vector-bundle and strict-perfect K for all scheme maps; locally-perfect K for maps between quasi-compact schemes; coherent G for flat maps between locally noetherian schemes |
| Waldhausen fibration | Change of weak equivalences with coarse two-out-of-three, extension, joint-cylinder data, and the second-endpoint section |
| Cofinality | Group-graded and dense-subcategory results with their explicit structural data; positive equivalences and degree-zero image statements |
| Algebraic Grothendieck group | Universal group of zero, weak-equivalence, and cofibration-pushout relations, without identification with homotopical K₀ |
| Homotopy foundations | Categorical fiber comparisons, additivity, finite HELP, weak-cartesian realization, and the stated compact lifting results |

See [Library.md](Library.md) for import paths and qualified interfaces.

## Perfect localization and degree zero

For an open immersion `j : U ⟶ X`, `Quillen.PerfectComplexes.PerfectOpenK j n`
uses the category of locally perfect complexes on `X`, with weak equivalences
detected by quasi-isomorphism after restriction to `U`. It is a relative model;
it is not the definition of `Quillen.PerfectComplexes.PerfectK U n`.
The general relative sequence uses the actual support-forgetting map and
homotopy-fiber boundary. Its surjective degree-zero map lands in
`PerfectOpenK j 0`.

For a principal open over an affine base, the relative-to-open map is bijective
in every positive degree and injective in degree zero. Its degree-zero target
is identified with exactly `(perfectKRestrict j 0).range`. The resulting group
sequence is exact through
`K₁(U) → K₀(X on X ∖ U) → K₀(X) → K₀(U)`, using locally-perfect K-theory.
Surjectivity onto the final `K₀(U)` is not asserted. The source theorems include
arbitrary commutative rings, zero divisors, and localization at zero.

The affine relative and supported strict/local comparisons allow arbitrary
opens of `Spec R`. They do not supply the absolute open endpoint for an arbitrary
open. See [ThomasonTrobaugh.md](ThomasonTrobaugh.md) for these distinctions.

## Open comparisons

- Strict versus locally-perfect equivalence on general nonaffine schemes.
- Absolute perfect K-theory endpoints for arbitrary quasi-compact opens,
  geometric density and replacement on general schemes, and global localization
  and descent beyond the affine principal-open case.
- Pullback on locally-perfect K-theory for arbitrary non-quasi-compact schemes;
  locally-perfect objects there need not have uniform cohomological bounds.
- Identification of homotopical K₀ with its algebraic Grothendieck presentation.
- General exact-category dévissage/localization beyond the implemented abelian
  and resolving-subcategory results.
- Full Serre-pair naturality with quotient and basepoint coherence.
- Cross-universe realization and model transport beyond the supplied explicit
  small-model equivalences and naturality statements.
- Plus-construction comparison, spectra, and nonconnective theory.

Regularity alone does not supply the resolution property on an arbitrary
scheme. Finite cube HELP does not imply arbitrary compact HELP, and endpoint
collar deformation alone does not provide vertical lifting. These boundaries
remain relevant when combining the existing results.

## Verification

`scripts/check.sh` builds every library module and the maintained `Tests`,
checks an independently configured downstream package, and explicitly replays
the transitive axiom audits. The allowed foundation axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The trust-discovery route is described in
[Architecture.md](Architecture.md#trust-checks).

Successful checks verify encoded statements and the audited foundation
dependencies in their covered environment.
Mathematical interpretation and the applicability of hypotheses still require
review. Passing the checks does not close an open comparison theorem.
