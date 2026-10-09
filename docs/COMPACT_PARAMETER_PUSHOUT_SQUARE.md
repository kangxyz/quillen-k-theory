# Actual compact-parameter pushout squares

**Author checked and frozen, 2026-10-09 14:19:09 UTC.** The source and all
**48 recursive defining origins / 20 consumers** passed warning-free.
Independent review remains pending; this source is beyond the frozen archive.

Source: `Quillen/Topology/Pushout/CompactParameterSquare.lean`.
Namespace: `Quillen.CompactParameterPushout`.

## Exact structural statement

For an original displayed `TopCat` pushout with vertex `P`, a continuous
`base : P → T`, and a continuous test `b : D → T`, all four corners are the
literal subspaces of pairs `(original point, d)` satisfying the corresponding
base-matching equation. Every new leg applies the original leg to its first
coordinate and leaves `d` unchanged. The original commuting equation supplies
only the necessary membership proof for the second incoming leg.

The main `isPushout` theorem retains `[LocallyCompactSpace D]` and the explicit
closedness of the original matching locus in `P × D`. Compactness of `D` is
not required when this closedness is supplied. There are no injectivity,
cofibration, nonempty-target, or lifting assumptions.

Separate corollaries cover a supplied closed graph of `b`, compact locally
compact tests into an actual simplicial realization, and the unchanged actual
displayed double-cylinder realization model. These use the previously proved
closed-graph theorems and retain the same literal matched square.

The topological objects and the parameter have a common arbitrary universe.
No cross-universe colimit preservation is claimed.

## Genuine universal-property proof

The original sum-of-legs matching quotient is already proved to carry the
actual pullback topology under precisely the displayed closed-locus/local-
compactness conditions. The ordinary sum/subtype homeomorphism and the literal
sum/product distribution identify its source with the sum of the two matched
outgoing corners. Thus their original matched leg sum is quotient.

For compatible maps from those matched corners to an arbitrary target `Z`,
fix the parameter `d` and form maps from the original corners to `Option Z`:
they are `some` of the supplied value when the point matches `b d`, and `none`
otherwise. The genuine original set-level pushout yields an `Option Z` map
on `P`. Its value at every matched point is actually `some`, as witnessed by
an original pushout representative. This constructs the descendant without
choosing an element of `Z`, even when `Z` is empty.

The descendant agrees exactly with the supplied maps on each matched leg.
Their genuine quotient map then proves continuity, with no separation
hypothesis on `Z`. Joint surjectivity proves uniqueness. These data construct
an actual `IsColimit` cocone and hence the exact displayed `IsPushout`.

## Validation contract

`audits/CompactParameterSquareAudit.lean` recursively audits every declaration
origin, including all private and generated helpers, allowing only the usual
three standard axioms. Its consumers retain each full coordinate formula,
parameter identity, original commutative square, quotient topology, both
universal-property equations and uniqueness. Empty parameters and an empty
cocone target are explicit. Original realization tests include points, every
finite cube, dimension zero, and the actual double-cylinder base.

The source reuses `Maps/SumSubtype` from the separate finite-cylinder boundary,
whose independent review must be accepted before this downstream boundary is
integrated. The other quotient and realization-model prerequisites already
have independent fresh reviews. No prerequisite source is changed.

Frozen manifest: `logs/compact-parameter-square-sources.sha256`.
Author terminal log: `logs/compact-parameter-square-audit-initial.log`.
Replay: `logs/verify-compact-parameter-square.sh`. The fixed48 guard is installed
for independent verification. The only first-check repairs moved `include sq`
before its documentation comment and replaced deprecated `dif_pos` spelling;
no mathematical hypothesis or universal-property argument changed.

## Scope limit

This is a restricted, proved base-change interchange for a locally compact
parameter with closed matching locus. It is not arbitrary pullback preservation
of topological pushouts, a weak-equivalence preservation assertion, compact
HELP, or the mixed open/closed gluing theorem. The latter must use the actual
parameter maps and supply this theorem's concrete hypotheses.
