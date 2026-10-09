# Independent review: actual bounded strata and cycle-to-term incidence

Accepted 2026-10-09 06:31 UTC after full semantic inspection and fresh isolated
rebuild of BoundedStrata, BoundedSSet, BoundedSSetColimit and
CycleEvaluationSequence. The four sources and all prior accepted dependencies
are unchanged from their author-checked boundaries.

Every bounded acyclic termwise-P complex has an actual symmetric term bound;
a finite family has a common bound derived by finite supremum. Increasing
stratum inclusions are genuine exact functors. They reflect inherited
inflations because the actual admissible quotient is termwise an epimorphic
image of the bounded target. Thus a finite ambient S-grid genuinely lifts,
including its quotient squares and weak maps, into one bounded stratum.

The actual bounded-acyclic S-set is proved to be the filtered colimit of these
concrete strata. Degreewise coverage and injectivity prove the universal
property. The previously verified filtered-realization results then give exact
compact-map factorization, factorization above a chosen bound, eventual map
equality and relative compact-homotopy lifting. No global uniform term bound,
stage equivalence or realization conclusion is assumed. Weak maps are retained
by inverse image; these coverage results do not require kernel closure.

The incidence file separately constructs the genuine exact evaluation functor
and original cycle inclusion/differential factorization Z_n → E_n → Z_(n+1).
Under actual kernel closure, quotient exactness proves the relative
cofibration condition. This is a structural cofibration sequence in the
isomorphism weak-equivalence models. It does not assert that evaluation or
cycles take quasi-isomorphisms to isomorphisms.

`audits/GilletWaldhausenCoverageIndependentAudit.lean` checks all 428 origins
across the full 19-source Gillet–Waldhausen boundary, including private/generated
helpers, and actual finite-grid/colimit/compact-homotopy/cycle-map consumers.
All checks are warning-free and allow only propext, Classical.choice and
Quot.sound. Fresh artifacts are in `/tmp/quillen-gw-coverage-independent-0628`,
first in LEAN_PATH. Evidence is in `logs/gw-coverage-independent-*`.
The four-source manifest SHA256 is
`d4cd711dc0f736cccd2875d061ae92c96d5a6c7297b56f1ed4decaf8e3429e87`.

These results are filtration and map-computation foundations. Both bounded
and acyclic isomorphism-model K-theories remain nontrivial graded theories;
their inclusion must be computed before applying a genuine fibration theorem.
The Gillet–Waldhausen equivalence remains open.
