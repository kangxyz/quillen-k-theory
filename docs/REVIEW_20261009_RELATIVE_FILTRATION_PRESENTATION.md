# Independent review: original relative-row filtration presentation

## Boundary and status

The boundary is `Fibration/RelativeRows/FiltrationEquivalence.lean` and
`FiltrationWeakEquivalence.lean`, frozen by
`logs/relative-rows-filtration-equivalence-sources.sha256` (manifest SHA-256
`9bc8f55bfed67dad4cad026ae3500027eed3dc3ed4421c16f4c5afa8cd098190`).
**Accepted.** The complete semantic inspection, fresh excluded-target
rebuilds, fixed59 recursive audit, and all28 strengthened consumers passed
warning-free. All source/dependency hashes remained unchanged. The serial
check acquired slot1 at 10:47:53 UTC and completed at 10:49:01 UTC.

## Semantic findings

1. The target objects form the actual full subcategory of the unchanged
   `ComposableArrows C n.len`: every original arrow is both a fine
   cofibration and a coarse weak equivalence. All natural transformations
   are retained before restricting the weak class.
2. The forward functor is literally the original initial filtration. The
   coarse extension axiom is used to prove its original arrows coarse-weak
   from the actual acyclic tail quotients. It is a structural axiom, not a
   presentation-equivalence assumption.
3. The inverse is the accepted actual chosen-zero augmentation followed by
   cofiber completion. Its maps are the original completed natural
   transformations. Identity and composition follow from those actual
   functors, rather than an unspecified equivalence choice. Completion
   itself does not require the extension axiom or saturation.
4. The chain-side natural isomorphism is the original quotient-by-zero
   comparison. The row-side isomorphism is its preimage under the accepted
   fully faithful original filtration functor, whose preimage is actual
   displayed-pushout descent. Naturality is checked on the original maps.
5. Restriction to the two wide subcategories uses genuine fine-map
   preservation in both directions. Forward fine weakness is also
   reflected. Unit and counit components are actual categorical
   isomorphisms, so both directions belong to the fine class. The
   coarse-only cylinder projection is not used as a fine morphism.
6. The classifying-space homotopy equivalence comes from this genuine
   equivalence of fine-weak categories. Its forward map is definitionally
   the original filtration classifying-space map; its inverse is
   definitionally the actual cofiber-completion map.

The object and hom universes remain independent. No kernel, cone, shift,
cylinder, or saturation assumption is added to this presentation theorem.
This is a degreewise unbased categorical/classifying-space result; it
neither assumes nor proves the global relative-realization homotopy fiber,
and makes no claim that the coarse cylinder projection is fine-weak or
that a chosen completion inverse is strictly outer-simplicial.

## Independent verification design

The first-path overlay excludes both target artifact families before
rebuilding them from the exact frozen source files. Other project artifacts
are read-only symlinks to the accepted dependency cache. The 311 dependency
sources and 467 dependency artifacts used by the source/audit import closure
are pinned and rechecked before and after. Target artifacts must be fresh
regular files, and dependency output must show that both rebuilt targets
are used.

The audit makes one traversal of declaration origins, requires exactly
59 declarations (26 + 33), and recursively permits only `propext`,
`Classical.choice`, and `Quot.sound`. Its 28 consumers cover literal
forward/inverse object and map formulas, original quotient-by-zero and
fully-faithful-descent components, fine-weak reflection/preservation,
original restricted functors, actual classifying-space forward/inverse
maps, degree zero, independent universes, bounded terms without kernel
closure, and arbitrary schemes.

- Replay: `logs/verify-relative-filtration-presentation-independent.sh`
- Driver: `logs/relative-filtration-presentation-independent-driver.log`
- Audit: `audits/RelativeFiltrationPresentationIndependentAudit.lean`
- Evidence directory: `logs/relative-filtration-presentation-independent-20261009/`

No implementation source, public definition, or live build artifact is edited
by this review.

Terminal evidence manifest: `logs/relative-filtration-presentation-independent-20261009/artifacts.sha256`.
