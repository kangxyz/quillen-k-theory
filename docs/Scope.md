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
| Perfect-complex models | Strict/local connective models, restriction and support maps, and change-of-cofibration comparison |
| Homotopy foundations | Categorical fiber comparisons, additivity, finite HELP, and the stated compact lifting results |

See [Library.md](Library.md) for import paths and qualified interfaces.

## Open comparisons

- Gillet–Waldhausen and strict versus locally-perfect comparison.
- Perfect-complex localization and the global change-of-weak-equivalences
  fibration theorem.
- Identification of homotopical K₀ with its algebraic Grothendieck presentation.
- General exact-category dévissage/localization beyond the implemented abelian
  and resolving-subcategory results.
- Full Serre-pair naturality with quotient and basepoint coherence.
- Arbitrary cross-universe realization and chosen-model transport.
- Plus-construction comparison, spectra, and nonconnective theory.

Regularity alone does not supply the resolution property on an arbitrary
scheme. Finite cube HELP does not imply arbitrary compact HELP, and endpoint
collar deformation alone does not provide vertical lifting. These boundaries
remain relevant when combining the existing results.

## Verification

CI builds every library module and the maintained tests, checks an independent
downstream package, and audits transitive axiom dependencies. The allowed
foundation axioms are `propext`, `Classical.choice`, and `Quot.sound`.

These checks certify encoded statements and their foundation dependencies.
Mathematical interpretation and the applicability of hypotheses still require
review. Passing the checks does not close an open comparison theorem.
