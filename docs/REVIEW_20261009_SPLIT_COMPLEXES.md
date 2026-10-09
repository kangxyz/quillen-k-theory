# Independent review: split complex models and actual factorizations

Reviewed 2026-10-09 independently of the implementation author. The frozen
scope is the nine modules in `logs/split-factorization-checked-sources.sha256`.
These remain separate from the 04:11 archive and await later public integration.

## Accepted mathematical endpoint

The ambient complex category and its actual strict-perfect, locally-perfect,
and supported full subcategories admit genuine Waldhausen structures with
actual quasi-isomorphisms and degreewise split monomorphisms whose quotient
lies in the selected subcategory. Splittings are global in each degree and
are not required to assemble into a chain map. The identity maps to the
ambient-monomorphism models are actual Waldhausen-exact functors and induce
genuine connective S-construction K-homomorphisms. Strict/local, restriction,
and support-forgetting maps are also constructed.

Every chain map between strict-perfect complexes, and every chain map between
locally-perfect complexes, factors inside the same category as a genuine split
cofibration followed by a quasi-isomorphism. The construction is explicit:
`K → Cone(id K) ⊞ L → L`. The second arrow is in fact a chain-homotopy
equivalence. The actual quotient of the first arrow is `Cone(-f)` and its
short exact sequence has a constructed splitting in every degree.

## Semantic review

- A pushout of a split mono is split by the explicit retraction obtained
  from its pushout universal property. Applying evaluation in each degree
  supplies split stability for complexes; evaluation preserves these pushouts.
- Multiplicativity, zero-source cofibrancy and isomorphism conditions are
  proved for degreewise split monos. Quasi-isomorphism gluing uses the
  accepted ambient-mono gluing theorem and the proved implication to mono.
- The subcategory cofibration is the intersection of the inherited exact
  cofibration condition with degreewise splitting. Thus quotient membership
  is retained. It is not silently replaced by an arbitrary split mono
  between objects of the subcategory.
- `splitSubcategoryCofibrations_iff` proves the exact degreewise split short-
  exact-sequence characterization, using the actual inherited inflation
  witness and degree evaluation in both directions.
- Comparisons are the original identity or full inclusion functors; their
  zero, cofibration, quasi-isomorphism and pushout preservation are supplied.
  Actual geometric restriction preserves the degreewise retractions.
- The factorization projection has a chain-homotopy inverse by the explicit
  contraction of the identity cone. The first factor has a termwise
  retraction. Its quotient map and section are written in actual cone and
  biproduct coordinates and satisfy the splitting identities in each degree.
- In a cone-closed exact full subcategory, the middle object belongs by cone
  and finite-biproduct closure, while the quotient belongs by closure applied
  to `-f`. These are legitimate closure hypotheses in the generic lemma;
  they are proved when it is applied to strict/local perfect complexes.
- Locally-perfect mapping-cone closure uses common open neighborhoods for
  strict local models and the previously proved distinguished-triangle local
  model theorem. It does not introduce a global strict representative or
  assume the desired cone-closure conclusion.

No semantic correctness blocker was found in this scope.

## Precise remaining scope

No change-of-cofibrations K-equivalence, Waldhausen approximation theorem,
Gillet–Waldhausen theorem, or localization sequence is proved here. A
factorization theorem alone is not those conclusions. Supported split
structures/maps are accepted; the stronger factorization theorem in this
review is explicitly for the strict and locally-perfect categories.

The locally-perfect object predicate still has no required uniform global
Tor-amplitude on non-quasi-compact schemes. Ordinary vector-bundle short
exact sequences need not split globally, so no unsupported degree-zero
exact functor from the full vector-bundle exact structure is asserted into
these split models.

## Independent Lean verification

The initial six frozen modules were rehashed and rebuilt with the focused
three-target build, which passed with 2,972 jobs. The independent origin audit
then passed all **95 declarations**, including private/generated helpers and
arbitrary-universe factorization, K-map and restriction consumers. A first
consumer harness omitted `noncomputable` on two example definitions; only
the audit harness was corrected, and the complete rerun exited with code 0.
The original diagnostic is retained as
`logs/split-complexes-independent-initial-harness.log`.

After the three factorization extensions, the focused rehash build of
`Quillen.PerfectComplexes.SplitFactorization` passed with 2,972 jobs.
`audits/SplitFactorizationIndependentAudit.lean` selects the exact nine module
origins, requires every module to contribute declarations, and checks each
transitive axiom closure. All **128 declarations** passed; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Arbitrary-universe strict/local
factorization examples also compile. The complete run exited with code 0.

Evidence:

- `logs/split-complexes-independent-build.log`
- `logs/split-complexes-independent-all-axioms.log`
- `logs/split-factorization-independent-build.log`
- `logs/split-factorization-independent-all-axioms.log`
- `logs/split-factorization-independent-final-hash-check.log`

The nine-source manifest still matches after the independent checks. Its
SHA-256 is `64fde746c760668568e804678c840a791c560cad1334a824ee8529dc8dd76fb5`.
The original six sources were unchanged by the extension or review. No
library proof source was modified by this independent review.
