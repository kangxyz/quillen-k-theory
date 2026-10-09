# Compact HELP two-of-three

## Contract

The new theorem boundary uses the existing
`CompactHomotopyExtensionLiftingProperty` unchanged. For every actual compact
pair `i : A ⟶ B` with the repository's homotopy extension property, a lift
extends the supplied map on `A` exactly, and its comparison homotopy agrees
with the **entire prescribed boundary homotopy at every time**.

For actual continuous maps `f : C(X,Y)` and `g : C(Y,Z)`:

- `CompactHomotopyExtensionLiftingProperty.cancel_first`: HELP for `f` and
  `g.comp f` implies HELP for the original `g`.
- `CompactHomotopyExtensionLiftingProperty.cancel_second`: HELP for `g` and
  `g.comp f` implies HELP for the original `f`.
- The two `compactHELP_comp_iff_of_*` theorems combine cancellation with the
  previously checked, unchanged composition theorem.
- `of_homotopy` and `compactHELP_iff_of_homotopic` prove genuine homotopy
  invariance, retaining the original maps as the theorem endpoints.
- `compactHELP_section` applies to an actual strict section of a HELP map.
  `compactHELP_transition` and its homotopy-commuting variant apply to the
  actual transition carrying one HELP section to another.

The HELP statements have the existing common universe `X Y Z : Type u`.
The explicit backtracking contraction separately permits independent
parameter and target universes. No compactness or separation assumption is
made on the entire spaces `X`, `Y`, or `Z`; compactness is only that of the
pairs quantified by HELP. No chosen global inverse family is used.

## Proof ingredients

`StrictCompact` proves equivalence with strict-square HELP, whose homotopy
is relative to the whole image of `i`. Full HELP follows by extending the
reverse of the supplied boundary homotopy, solving the resulting strict
square, and removing the temporary constant prefix through the existing
relative interval-square extension theorem.

`RetraceBoundary` contracts a reversed path followed by itself by shrinking
both traversals together. Its dependence on the parameter is continuous,
and both endpoints stay fixed. `CancelFirst` lifts the boundary through
`f` using the empty compact cofibration, applies HELP for `g.comp f`, and
extends the boundary adjustment by HEP. The explicit backtracking
contraction corrects the resulting homotopy to be relative to the boundary.

`CylinderBoundary` constructs the actual topological pushout of `A × I`
and `B ⊕ B` over `A ⊕ A`. Compactness follows from the original topological
pushout, without Hausdorff hypotheses. HEP of its map to `B × I` follows
from the checked relative interval-square extension. No embedding of `i`
is assumed. `CancelSecond` applies HELP for `g` to this compact pair; the
obtained continuous map has precisely the required endpoints and original
side homotopy.

## Actual split-fiber application

`Realization/SplitFiberCompactHELP` proves that the unchanged
`SplitRealizationFiber.inclusion` is a literal section of its actual
`firstProjection`, and hence has compact HELP from the genuine row
comparison equivalence. The inclusion's source coordinate is the original
realized split map and its path remains the original constant path.
`transition_compactHELP` then applies to an actual transition satisfying the
strict split triangle. The hypotheses are the original row equivalences
and split diagrams; there is no assumed fiber equivalence or HELP
conclusion.

This boundary supplies local HELP input. It does not establish a
fiberwise-to-total HELP theorem, a weak-cartesian cube theorem, or global
bar/gluing conclusions.

## Verification

All eight ordered source checks passed warning-free. The recursive
all-origin audit passed **43** defining origins, including private and
generated declarations, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. All **28** consumers checked: both cancellation directions,
strict/full boundary statements, independent-universe retracing, actual
pushout/cylinder maps and compactness, homotopy invariance, strict and
homotopy-commuting section comparisons, and unchanged realized split-source
and constant-path coordinates. The final fixed43 guard rerun also passed warning-free.

- Frozen manifest: `logs/compact-help-two-of-three-20261009/sources.sha256`.
- Manifest fingerprint:
  `4dea5a2aeb21d3cc62027a42975eb862399e346cad8ce0da192998ecc3e7ce28`.
- Audit: `audits/CompactHELPTwoOfThreeAudit.lean`.
- Ordered checks: the eight `*-final.log` files in the evidence directory,
  all empty on successful warning-free compilation.
- Audit logs: `audit-initial.log` and `audit-final.log`.
- Lock acquisition record: `acquisition.log`.
- Accepted prerequisite hashes: `prerequisites.sha256`, including unchanged
  `Composition.lean`; all rechecked after the final fixed-count audit.
- Scripts: `logs/check-compact-help-two-of-three-final.sh` and
  `logs/audit-compact-help-two-of-three-final.sh`.

Evidence directory: `logs/compact-help-two-of-three-20261009/`.
All checks used the shared slot1 lock and single-threaded Lean; no broad Lake
build was run. This is the author's checked theorem boundary, pending the
parent's separate independent review.
