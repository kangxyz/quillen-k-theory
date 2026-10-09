# The canonical exact-category Quillen Q / Waldhausen S comparison

## Endpoint

The comparison is now proved for an arbitrary category `C : Type u` with
`Category.{v} C`, `Preadditive C`, `HasFiniteBiproducts C`, and an actual
`Quillen.ExactStructure C`. There is no abelian, balanced, idempotent-complete,
or comparison-equivalence hypothesis.

Import `Quillen.Waldhausen.QuillenComparison.Equivalence`.

* `rowChainEquivalence E n` is the actual categorical equivalence from exact
  `S_(2n+1)` rows and their natural isomorphisms to the core of finite Q-chains.
  Its functor is the originally defined `rowChainComparison`.
* `realizationComparisonHomotopyEquiv E` is a homotopy equivalence from the
  edgewise-subdivided original S realization to the original Q realization.
  Its forward continuous map is **definitionally** `realizationComparison E`.
* `deloopingHomotopyEquiv E` gives the homotopy equivalence between the existing
  S-delooping and Q-space through the canonical edgewise zigzag.
* `comparisonKEquiv E n : (ofExactCategory E).K n ≃* E.K n` is the isomorphism
  between the two already-defined K-groups. Its underlying homomorphism is
  **definitionally** the previously constructed `comparisonK E n`.

The two forward maps of the realized zigzag preserve the chosen zero
basepoints by proved equalities. The K-equivalence is assembled from those
two based group isomorphisms, rather than assuming that a chosen homotopy
inverse on spaces preserves the basepoint.

## Proof content

1. Genuine exact rectangles give the admissible spans and their pullback
   composition. Reindexing and vertical isomorphisms define the canonical
   edgewise simplicial comparison.
2. The actual S simplicial set is identified with the diagonal nerve of its
   exact-row groupoids.
3. Full faithfulness is proved by recovering both endpoints of every initial
   subobject. An apex isomorphism recovers the upper endpoint; the actual
   kernel recovers the lower endpoint. Central intervals cover every index.
   Monicity forces coherence and actual cokernel descent extends the flag
   isomorphism to the entire row. Epic cancellation verifies the prescribed
   quotient components.
4. Essential surjectivity is an induction on Q-chain length. A genuine span
   representative of the next arrow pulls back the previous admissible flag.
   Prefixing zero and adjoining the new target yields an admissible extended
   flag. Its actual cokernels form an exact row. Kernel/cokernel universal
   properties identify the middle row, and the explicit terminal-span
   calculation verifies exactly the new Q-arrow. No row-lifting hypothesis
   is assumed.
5. Mixed-hom-universe nerve realization, the generic rowwise-to-diagonal
   realization equivalence, partial edgewise subdivision, and the explicit
   classification-diagonal contraction give the homotopy equivalence.
   `comparisonMap_factorization` is an equality of the actual simplicial
   maps, proved by `rfl`.

## Source and checking evidence

The final implementation sources are frozen in
`logs/q-s-comparison-final-sources.sha256`: 41 modules under
`Quillen/Waldhausen/QuillenComparison/`, including the separately authored
functoriality module, and the post-migration revision of `SpecialFractions`.
Manifest SHA-256:
`c85dbd2382a2bae9f96b4584ec32450f51afc4a3f4729f029196e40d18c23047`.

`SpecialFractions.lean` is frozen at
`e4a0ba32598382da60afa029d48400d5ecd2a3b3f6b137d3e8e335c94e95f931`.
Its primitive admissible-epi-plus-mono, exact short-five, and pullback
arguments were read semantically and are included in the recursive
standard-axiom audit. This is the post-migration proof revision, not a claim
that its bytes equal the historical migration snapshot.

The final induction and equivalence modules compile without warnings:
`logs/quillen-comparison-Equivalence.log`. The earlier independently frozen
26-module source manifest still revalidates. Independent semantic reviews
cover full faithfulness, quotient completion, pullback flag extension,
terminal-span reconstruction, induction, and the exact-map/topological
assembly. Their reports are separate from this implementation report.

### Completed full-origin audit

The independent `audits/QuillenSComparisonIndependentAudit.lean` completed
successfully: **766 declarations across 43 defining modules**, including the
42-source manifest and the Q-core support module. Recursive axiom collection
accepted only `propext`, `Classical.choice`, and `Quot.sound`. Its log is
`logs/q-s-full-independent-audit.log`. Generic-universe consumers check the
actual equivalence, the exact forward map, both chosen basepoints, and the
canonical K-homomorphism identity. The separate final-endpoint review also
recompiled both final sources warning-free and audited their 31 defining
constants; see `docs/REVIEW_20261009_QS_EQUIVALENCE.md`.

The implementation-side repeated-scan audit was interrupted and supplies no
completed evidence. Its original driver and the later unvalidated one-pass
draft are distinguished in `logs/q-s-comparison-audit-script-history.txt`.
The validation evidence cited above is the completed independent audit.

## Scope

There is no remaining mathematical gap in this Q/S comparison endpoint.
The separate Gillet–Waldhausen and strict-versus-local perfect-complex
comparisons are not consequences claimed by this module. The proved Q/S
isomorphism can now be composed with the accepted small-vector-bundle
Q-model equivalence and the existing genuine S-model functors.
