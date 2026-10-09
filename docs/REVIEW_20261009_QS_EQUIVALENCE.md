# Independent review: the canonical exact-category Q/S equivalence

Date: 2026-10-09 (UTC).

## Accepted endpoint

The actual central-interval comparison is a categorical equivalence in every
row. Its original simplicial comparison map realizes to a homotopy equivalence,
and the already-defined canonical comparison homomorphism is the underlying
homomorphism of `comparisonKEquiv` for every natural-number K-degree.
No equivalence hypothesis is an input of these final endpoints.

Exact reviewed sources:

- `Quillen/Waldhausen/QuillenComparison/RowEssentialSurjective.lean`
- `Quillen/Waldhausen/QuillenComparison/Equivalence.lean`

Manifest: `logs/review-20261009-qs-equivalence-sources.sha256`.

## Semantic verification

The zero-length chain is represented by the actual admissible flag zero to its
specified object. In the induction step, the last old central quotient is
identified with the whole initial flag. The new arrow is transported through
this identification and the previous chain isomorphism, and a genuine
admissible-span representative is chosen in the existing Q-arrow quotient.
Pulling back the old admissible flag along its deflation and adjoining zero
and the new target produces the next row. The terminal-span identity verifies
the precise last square needed to extend the chain isomorphism; equality of
objects alone is not used as a substitute. This proves essential surjectivity,
which combines with the previously proved fullness and faithfulness.

The topological assembly uses the generic rowwise-to-diagonal realization
homotopy-equivalence theorem with the exact postcomposition nerve maps of
these categorical equivalences. The row-model isomorphisms, upper-index
restriction and classification-diagonal evaluation are the previously checked
model changes. Their composite is proved equal to the original comparison map.
The final homotopy equivalence explicitly retains that continuous map as its
forward function.

Both legs of the original comparison zigzag preserve the chosen zero points.
The K-group equivalence is formed by inverting the left leg's induced group
isomorphism and composing the right leg's induced group isomorphism. Thus the
proof does not incorrectly require a chosen inverse continuous map to preserve
the chosen point. Its underlying homomorphism is definitionally the earlier
`comparisonK`, with the same zigzag characterization.

`Factorization`, `RowBase`, the index/chain-extension definitions, and the
reconstructed-row/terminal-span formulas were also read for this semantic
review. Their source checks and complete origin scopes are recorded separately
by their owners and the final integration audit.

## Lean verification

- Both exact-hash source files were rebuilt directly with matching oleans,
  warning- and error-free, under compiler slot 2. Hashes matched before and after.
- `audits/Review20261009QSEquivalenceAudit.lean` recursively audited all 31
  declaration origins, including private/generated declarations. Only
  `propext`, `Classical.choice` and `Quot.sound` occurred. Its scope is count-frozen
  at 31.
- External consumers checked row equivalence with exactly the prescribed
  functor; actual chain preimages; the realized homotopy equivalence and exact
  forward function; chosen-basepoint preservation; the K-group equivalence and
  its exact original homomorphism; and the based zigzag identity. Object and
  hom universes remain independent and arbitrary.
- Universe-sensitive scheme consumers additionally checked that the public
  small-model Scheme.K composes with the inverse Q/S equivalence to actual
  vector-bundle S-theory, and then with the existing homomorphism to PerfectK.
  No raw cross-universe realization assertion was required.
- Logs: `logs/review-20261009-qs-equivalence-check.log` and
  `logs/review-20261009-qs-equivalence-audit.log`.

This is a focused endpoint verification, not a new full-project rebuild.

## Scope boundary

The endpoint proves the connective exact-category Q/S comparison. It does not
assert a homeomorphism of realizations, nonconnective K-theory, normalized based
K-map naturality for exact functors, Gillet–Waldhausen, strict/local perfect
comparison, or equivalence of the resulting Scheme.K-to-PerfectK map.
