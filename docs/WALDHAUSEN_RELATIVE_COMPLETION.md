# Actual generic relative-row completion

## Contract

The three sources frozen in `logs/relative-rows-completion-sources.sha256`
construct genuine quotient rows from original finite cofibration chains in
an arbitrary Waldhausen category, in independent object and morphism universes.

- `RelativeRows.zeroAugmentFunctor` adjoins the actual chosen zero and retains
  every original positive-index object, arrow, and transformation component.
- `QuotientRows.cofibrationArrowDiagram` uses the original arrows as actual
  extension-category objects. Horizontal maps satisfy the genuine Reedy
  cofibration condition. Every displayed interval square is an actual pushout
  in the extension category: its source square is identity-horizontal and its
  target square identity-vertical.
- `QuotientRows.completeCofibrationFlag` applies the already-proved exact
  cofiber functor. Its diagonal objects are genuinely zero; its cofibrations
  and quotient squares follow from that exact functor and the displayed
  extension-category squares.
- `RelativeRows.relativeCompletion` turns a fine-cofibration/coarse-weak chain
  into a genuine relative row. Tail acyclicity follows from original coarse
  gluing, with no extension or saturation hypothesis.
- `relativeCompletionInitialIso` recovers the original initial filtration
  through the literal original quotient-by-zero projections. Arbitrary
  transformations are completed functorially at the quotient-row level;
  pointwise fine weak maps remain fine weak by genuine cofiber exactness.

No exact-category, abelian, projectivity, boundedness, or kernel-closure
hypothesis enters this generic construction. Consequently it also applies to
actual quotient-row Waldhausen categories, provided the chain arrows satisfy
that category's genuine Reedy cofibration predicate. This does not turn raw
pointwise finite-chain cofibration evidence into Reedy cofibration evidence;
the genuine row-cylinder factorization remains a separate construction.

## Verification

All three defining sources passed focused direct Lean checks warning-free.
The terminal fixed86 single-pass audit passed all86 origins (32 + 33 + 21)
and14 actual-map/minimal-input consumers with only the standard three axioms.
The origin/consumer audit is `audits/RelativeRowsCompletionAudit.lean` and its
terminal evidence is recorded in `logs/relative-rows-completion-audit-final.log`.
The audit includes independent universes, original quotient projections and
pushouts, actual inner-row-category use, and the actual bounded-term complex
model without a kernel-closure hypothesis. Independent review passed: fresh three-source rebuild, fixed86 recursive
origins and21 strengthened consumers, all warning-free with unchanged hashes.

A separate `FiltrationEquivalence.lean` development combines this construction
with the accepted original-filtration full faithfulness. Only the reverse
recognition of relative rows as coarse-weak chains uses the structural coarse
extension axiom. It is outside the frozen three-source boundary.
