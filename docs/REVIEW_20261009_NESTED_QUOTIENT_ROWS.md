# Independent review: nested weak classes on original quotient rows

## Semantic contract

Reviewed the frozen source
`Quillen/Waldhausen/Fibration/Rows/NestedWeakEquivalences.lean` and its actual
row gluing/evaluation/reindexing prerequisites. No semantic issue was found.
The source manifest is `logs/nested-quotient-rows-independent/sources.sha256`.

The new coarse structure uses precisely the existing fine quotient-row
objects and natural transformations. Its cofibration class is literally the
existing Reedy class, and its chosen zero is literally the existing zero row.
Only its weak-equivalence predicate changes, to the original pointwise
coarse predicate.

The proof of coarse gluing evaluates the genuine original row pushouts,
uses the actual component cofibrations through the explicit base class
equality, and applies the original coarse Waldhausen gluing axiom. It does
not mistake pointwise cofibration evidence for a Reedy cofibration. The
inherited pushout existence and cofibration-pushout closure remain those of
the original fine row structure.

The genuine nested-row package retains these literal cofibration/zero data
and proves fine weakness implies coarse weakness componentwise. Original
evaluation and ordinal reindexing functors are genuinely exact, including
preservation of the actual displayed pushout squares. Coarse two-out-of-three
is derived componentwise using coarse base two-out-of-three alone.

No extension, cylinder, factorization, fine saturation, or fibration
hypothesis is present. Object and morphism universes remain independent.
The same construction can be iterated on the actual quotient-row categories.

## Independent verification

The fresh first-path project overlay excludes every artifact of the target
module before building it. All imports of the audit use that freshly built
target; accepted dependencies are linked in the same project-prefix overlay.
The exact script, import paths, logs, source hashes, and dependency hashes are
in `logs/nested-quotient-rows-independent/`.

`audits/NestedQuotientRowsIndependentAudit.lean` checks all20 defining origins,
with a fixed20 guard and recursive axiom collection. The author’s15 consumers
are retained and5 independent consumers add actual iterated row structures,
literal twice-pointwise coarse weakness, actual evaluated cofibrations,
coarse-only postcomposition cancellation, and original row isomorphisms.
The entire28-module Quillen source closure and33 used dependency artifacts
are hashed separately.

The source rebuild passed warning-free. The initial fixed20 origin audit was
also clean; a strengthened driver-only cancellation consumer needed its
second morphism predicate named explicitly. No frozen source was changed.
**Accepted.** The corrected fixed20 recursive audit and all20 consumers
passed warning-free on the fresh target, with no errors or `sorryAx` and
only the standard three axioms. Target pre/post hashes and the complete
source/dependency-artifact hashes all match.
