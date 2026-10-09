# Actual relative-row quotient and product section

## Contract

For an arbitrary genuine Waldhausen structure `V` on `C : Type u` with
`Category.{v} C`, and actual nested weak-equivalence structure `N`, the
relative quotient-row category has the following actual constructions.
No cylinder, saturation, extension, realization-equivalence, or fibration
hypothesis is used.

`RelativeRows.TailQuotient` retains the original row and interval maps.
Its quotient functor is literally `tailFunctor N n ⋙ tailSection N n`.
The natural transformation `tailProjection` is the original interval map
induced by raising the added vertex to the first tail vertex and fixing all
tail vertices. Every component cofiber square is an actual categorical
pushout: initial intervals use the original row quotient square, while
zero and strictly positive intervals use actual zero-object isomorphisms.

`cut_tail_isCofibrationSequence N n` proves the genuine structural sequence
`cutFunctor → identity → tailQuotientFunctor`. In particular, its relative
cofibration condition is the already-proved original cutoff condition, and
its cofiber square uses the chosen relative zero object. This does not
replace the structural condition by pointwise cofibrations.

`RelativeRows.ProductSection` defines the original exact functor
`splitFunctor N n` from `C × tailRows` to relative rows. Its object is the
chosen coproduct of `tailSection(second)` and `fiber(first)`, in that order;
its maps are exactly the coproduct maps of the original functor maps.
Any chosen binary coproducts work, and the actual Waldhausen structure
provides such a choice without an additional existence hypothesis.

`splitFirstTailIso N n` identifies `splitFunctor ⋙ firstTail` with the
identity functor. Its inverse is literally the pair consisting of the
first evaluation of the fiber coproduct inclusion and the tail evaluation
of the tail-section coproduct inclusion. These maps are proved invertible
using mapped actual pushouts and the actual zero first object / zero tail.
The other composite satisfies the strict functor equality
`firstTail_splitFunctor`: it is the pointwise coproduct of the actual tail
quotient and `first ⋙ fiber`. Combining this with the separately constructed
`firstFiberCutIso` supplies the inverse candidate for relative additivity.

## Scope and verification

Both constructions retain independent object and morphism universes and
include outer degree zero. The separate realization assembly uses actual
additivity; neither source here assumes or concludes a fibration theorem.

Audit and frozen-source evidence are recorded in
`audits/RelativeRowsTailSectionAudit.lean` and
`logs/relative-rows-tail-section-sources.sha256`. The audit checks every
source-origin declaration recursively and actual quotient arrows,
cofiber squares, functor maps, inverse maps, and both isomorphism identities.

Both sources compile warning-free. The initial audit passed all26 defining
origins and all15 consumers with only `propext`, `Classical.choice`, and
`Quot.sound`; its fixed26 confirmation also exited0 without warnings or errors in
`logs/relative-rows-tail-section-audit.log`. All frozen source and relative
prerequisite hashes match in `logs/relative-rows-tail-section-hashes.log`.
Independent review passed jointly with the seven cutoff sources; see
`docs/REVIEW_20261009_RELATIVE_CUT_SECTION.md`. The independent fresh build,
fixed77+26-origin audits, all36 consumers, and source rehashes passed.
