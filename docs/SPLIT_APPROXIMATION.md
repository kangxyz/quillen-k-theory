# Change of cofibrations for actual perfect-complex models

## Checked mathematical endpoint

The 15 sources in `logs/split-approximation-checked-sources.sha256` construct
an actual homotopy equivalence between the original S-construction
realizations for split and ambient cofibrations on a cone-closed full
subcategory of cochain complexes in an arbitrary abelian category.

`splitDeloopingHomotopyEquiv P hcone` is the equivalence.
`splitDeloopingHomotopyEquiv_toFun` identifies its forward continuous map
with the previously defined canonical `deloopingMap` of the identity exact
functor. No homotopy-equivalence conclusion is supplied as a hypothesis.

Required object-predicate hypotheses are: containing zero, closure under
isomorphisms, extension closure in the ambient abelian exact structure,
closure under finite products, and actual mapping-cone closure. These are
structural properties of objects, not comparison conclusions.

## Proof route

1. The identity-cone factorization is a functor on the actual arrow category,
   with natural inclusion and projection. Its middle object and quotient
   stay in the full subcategory by the accepted nine-source split model.
2. Recursive replacement on natural-number sequences, then finite
   restriction, constructs finite split-cofibration flags functorially.
   The projection is pointwise a quasi-isomorphism. Two-out-of-three proves
   that replacement preserves arbitrary pointwise weak-equivalence maps.
3. The category of weak-equivalence flags has actual natural comparison
   transformations in both directions. Their realized homotopies prove
   that the canonical flag inclusion is a homotopy equivalence.
4. Canonical cokernel completion constructs actual quotient rows. Its
   horizontal maps are pushouts of the original chosen cofibrations.
   Quotient transformations preserve weak equivalences by Waldhausen
   gluing on actual cokernel pushouts. The argument uses arbitrary natural
   transformations, not only natural isomorphisms.
5. Quotient universal properties provide natural row/flag comparisons.
   This gives a genuine homotopy equivalence for the canonical inclusion
   of pointwise-quasi-isomorphism quotient-row categories in every degree.
6. `weakRowDiagonalIso` identifies the original grid S-construction
   simplicial set with the diagonal of the actual row nerve. Its inclusion
   naturality preserves the canonical map exactly.
7. The independently accepted generic theorem
   `BisimplicialRealization.diagonalRealizationHomotopyEquiv` turns these
   row equivalences into the actual original-grid equivalence. No
   simplicially coherent choice of rowwise inverse is assumed.

## Standard approximation theorem and scope

Waldhausen's original approximation theorem 1.6.7 and Thomason–Trobaugh
1.9.1 require an exact functor, saturation of weak equivalences, a source
cylinder functor satisfying the cylinder axiom, reflection of weak
equivalences (App1), and the approximation factorization property (App2).
TT's version permits a non-cofibration first factor in App2 because the
cylinder supplies a cofibration replacement. TT 1.9.2 applies this to the
change from degreewise split cofibrations to ambient cofibrations.

Primary references:
- Waldhausen, *Algebraic K-theory of spaces*, theorem 1.6.7:
  https://www.math.uni-bielefeld.de/~fw/LNM1126_318-419.pdf
- Thomason–Trobaugh, *Higher algebraic K-theory of schemes and of derived
  categories*, sections 1.3, 1.9.1–1.9.2:
  https://gwern.net/doc/math/1990-thomason.pdf

The implementation proves App1, cofibration-App2, saturation, functorial
factorization, the joint-endpoint split sequence, and a relative split-mono
lemma. It does not assert that these alone constitute a complete cylinder
functor, and it does not assert the general Waldhausen approximation
theorem. The special change-of-cofibrations theorem instead follows from
the independent finite-flag proof above.

This does not prove a strict-perfect versus locally-perfect comparison,
Gillet–Waldhausen, localization, or a nonconnective spectrum comparison.
It retains the existing pointwise-local perfectness convention; uniform
global Tor-amplitude on non-quasi-compact schemes is a separate issue.

## Verification and source boundaries

All 15 manifest sources compiled individually on the pinned toolchain,
serially under `/tmp/quillen-lean-slot-2.lock`. The recursive source-origin
axiom audit covers all 377 declarations, including generated/private ones:
only `propext`, `Classical.choice`, and `Quot.sound` occur.

- Audit: `audits/SplitApproximationAudit.lean`
- Evidence: `logs/split-approximation-axioms.log`
- Frozen hashes: `logs/split-approximation-checked-sources.sha256`

Canonical quotient machinery is shared with the Q/S comparison worker in
`Quillen/Waldhausen/QuillenComparison/`. The nine previously accepted split
sources and all previously accepted public umbrellas remain unchanged.
The 15-source branch passed independent semantic review. The K-map
and scheme-consumer extension is recorded separately below.

## Canonical K-map endpoint: two additional files

The 15-source realization branch has now passed the parent's independent
semantic review, focused rebuild, 377-declaration audit, and arbitrary-universe
strict/local realization consumers with exact forward-map checks.

Two further checked sources are frozen separately:

- `Quillen/Waldhausen/Approximation/SplitKEquivalence.lean`
- `Quillen/PerfectComplexes/SplitComparison.lean`

The first proves `splitComplexSubcategoryKMap_bijective P hcone n` and
constructs `splitComplexSubcategoryKEquiv P hcone n`. Crucially, the theorem
uses the existing `splitComplexSubcategoryKMap`, whose definition includes
canonical zero-object rebasing. The unique isomorphism of the unchanged
chosen zero is the identity; `splitComparison_rebaseFunctor_eq` and
`splitComparison_rebased_deloopingMap` prove that the rebased functor and
realization map are exactly the original identity comparison. The actual
homotopy-equivalence theorem for homotopy groups then gives bijectivity.

The scheme-level module supplies, for every `Scheme.{u}` and every `n : ℕ`:

- `splitStrictToStrictKMap_bijective X n`
- `splitPerfectToPerfectKMap_bijective X n`
- `splitStrictKEquiv X n : SplitStrictK X n ≃* StrictK X n`
- `splitPerfectKEquiv X n : SplitPerfectK X n ≃* PerfectK X n`

Each equivalence's `toMonoidHom` is exactly the previously defined canonical
comparison homomorphism. All cone-closure hypotheses are discharged by
proved strict-perfect and locally-perfect mapping-cone closure.

Build evidence: `logs/split-k-equivalence-build.log` (successful, empty).
Two-source frozen manifest: `logs/split-k-comparison-checked-sources.sha256`.
Combined source-origin audit: `audits/SplitKComparisonAudit.lean`, with log
`logs/split-k-comparison-axioms.log`. All 417 declarations passed with only
`propext`, `Classical.choice`, and `Quot.sound`, including generated/private
declarations; the arbitrary-universe locally-perfect K-map consumer passed.
The full 17-source endpoint has now passed independent semantic review,
fresh isolated wrapper checks, all 417 source-origin declarations, and
arbitrary-universe strict/local consumers. See
`docs/REVIEW_20261009_SPLIT_MODEL_EQUIVALENCE.md`.
