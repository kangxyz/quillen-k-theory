# Independent review: exact-functor Q/S naturality

Date: 2026-10-09 (UTC).
Source: `Quillen/Waldhausen/QuillenComparison/Functoriality.lean`.
Frozen manifest: `logs/q-s-functoriality-sources.sha256`.

## Semantic result

Accepted within the stated raw simplicial-map scope.

`exactPostcompSimplex` preserves the original zero diagonals by additive-functor
zero preservation and takes each inflation to its exact-functor image. It does
not hypothesize preservation of the S-pushout. Instead it maps the genuine
conflation proved from the old quotient square, obtains the new cokernel
universal property from the target exact structure, and reconstructs the actual
pushout with its mapped zero vertex. Original vertical isomorphisms remain
isomorphisms under the functor.

`exactSSetMap` is literal grid postcomposition. Its identity and composition
laws identify the actual simplicial maps. Its agreement with the general
Waldhausen `sSetMap` is proof-irrelevant equality of the same construction when
that adapter's exactness proof is supplied; this optional agreement hypothesis
is not an assumption of `exactSSetMap` or of comparison naturality.

The termwise interval-span identity and exact vertical-isomorphism formula
identify the complete Q-valued grid with postcomposition by `F.mapQ`. Hence
`comparisonMap_naturality` is strict equality of the original simplicial maps,
including the nerve direction and every actual Q-arrow.

The theorem retains arbitrary independent object and hom universes, shared by
the source and target categories as declared. It does not assert naturality of
normalized based K-maps; a functor's zero object is only canonically isomorphic
to the target chosen zero, and that separate normalization is not addressed.

## Verification

- The source manifest matched before and after an independent direct Lean
  rebuild with matching olean. The source-check log is empty: no warnings or errors.
- All 11 declaration origins passed recursive axiom collection, allowing only
  `propext`, `Classical.choice` and `Quot.sound`. The audit is count-frozen at 11.
- Arbitrary-universe consumers checked the exact postcomposition formula,
  identity/composition, agreement with `sSetMap`, and the exact raw comparison
  naturality equation. No implementation edits were made.
- Audit: `audits/Review20261009QSFunctorialityAudit.lean`.
- Logs: `logs/review-20261009-qs-functoriality-check.log` and
  `logs/review-20261009-qs-functoriality-audit.log`.
