# Independent review: the original S-grid weak-row nerve presentation

Accepted on 2026-10-09. The three frozen production sources remain unchanged;
ordered hashes are in `logs/row-nerve-presentation-independent/sources.sha256`.

## Semantic findings

All297 defining lines and the prior GridBridge interface were read. The
forward functor reads the original rows and original nerve-direction maps.
The inverse reconstructs each mixed grid arrow from its original row arrow
followed by its original nerve component. Its composition law is proved by
actual naturality, and the row and nerve arrows are recovered exactly.
The original zero/cofibration/pushout/weak predicates are checked on this
same reconstruction. The two inverse laws are genuine functor equalities;
the right-inverse proof explicitly handles object equality transport through
the original component maps. No predicate equivalence is substituted for
an actual equivalence of simplices.

The simplex equivalence commutes strictly with both original ordinal
restrictions and gives genuine bisimplicial and diagonal isomorphisms from
the existing S-construction. Postcomposition retains the original exact
functor and its actual maps. Both naturality squares use the existing
bisimplicial S-map and S-map. No saturation, extension, cylinder, equivalence
conclusion or fibration conclusion is assumed. Structural postcomposition
allows distinct source/target object and hom universes; the simplicial
naturality statements retain the original common source/target universe
scope. The actual relativeSRows consumer is included.

## Fresh verification

A first-path isolated overlay excluded all three target artifact families
before fresh serial rebuilds. No live compiled target or production source
was changed. All source checks and the fixed75-origin recursive audit
(43+19+13) passed warning-free with only the standard logical axioms.

All29 consumers passed: the author's22 plus seven independent checks of the
literal inverse mixed arrow, inverse ordinal naturality in both directions,
actual-zero reconstruction, original nerve arrow, degree-zero inverse and
cross-universe exact-functor morphism components. All55 dependency source
hashes and164 actual prerequisite artifact hashes were rechecked, as were
the original three production hashes.

The driver is `audits/RowNervePresentationIndependentAudit.lean`. The
reproducible harness, actual first-path import evidence and all logs/hashes
are in `logs/row-nerve-presentation-independent/`. This acceptance closes the
original-grid/weak-row-nerve presentation gap; it does not by itself assert
the separate total mixed comparison or global fibration theorem.
