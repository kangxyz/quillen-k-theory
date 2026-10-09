# Genuine original-filtration presentation equivalences

## Underlying categories

`Fibration/RelativeRows/FiltrationEquivalence.lean` uses the full subcategory
of the unchanged `ComposableArrows C n.len` category consisting of chains
whose actual arrows are fine cofibrations and coarse weak equivalences.
There is no replacement of the underlying chain morphisms.

The forward functor `filtrationPresentation` is the original
`initialFiltrationFunctor`, with only these proved object predicates added.
The inverse `completionFunctor` is the actual zero-augmentation/cofiber
completion. Its identity and composition laws follow from the unchanged
zero-augmentation and cofiber functors.

The chain-side natural isomorphism consists literally of the original
quotient-by-zero maps. The row-side natural isomorphism is their unique
extension through the original displayed quotient pushouts, using the
accepted fully faithful original-filtration functor. These genuine natural
isomorphisms prove `filtrationEquivalence` without any equivalence hypothesis.
The equivalence retains both displayed functors literally.

## Fine-weak morphism categories and realization

`FiltrationWeakEquivalence.lean` restricts the original objects to the actual
fine-weak morphism categories, via mathlib's existing `WideSubcategory`.
Fine weakness on rows is exactly detected by original initial components;
completion preserves it by actual cofiber gluing. The natural isomorphisms
remain in the weak categories because actual isomorphisms are fine weak.

`weakFiltrationEquivalence` is therefore a genuine equivalence of those
actual weak-map categories. `weakFiltrationClassifyingHomotopyEquiv` follows
from the accepted categorical-equivalence realization theorem. Its forward
map is literally the classifying-space map of the unchanged original
weak-filtration functor; its inverse is the actual completion functor's map.
No arbitrary product-realization theorem is used.

## Exact hypothesis boundary

All categories permit independent object and morphism universes. The sole
extra structural hypothesis is `ExtensionAxiom N.coarse`, used to prove that
an existing relative row's original filtration arrows are coarse weak.
Completion itself, full faithfulness, and fine-weak detection need neither
extension nor saturation. No cylinder, factorization, exact-category,
abelian, projectivity, global boundedness, or kernel-closure assumption
enters these generic presentation equivalences.

The actual bounded-term iso/quasi model satisfies the structural extension
axiom by the already-proved complex extension theorem, with no kernel
closure. The generic presentation also applies to genuine inner row
categories once their structural coarse extension axiom is proved.

These results do not identify arbitrary coarse-weak chains with cofibration
chains on fine-weak nerves. In particular, a cylinder replacement's coarse
projection does not become a fine natural transformation. The genuine
mixed comparison and eventual diagonal fibration remain separate.

## Verification

Both focused defining-source checks and the fixed-origin/actual-map audit
are recorded in `logs/relative-rows-FiltrationEquivalence.log`,
`logs/relative-rows-FiltrationWeakEquivalence.log`, and
`logs/relative-rows-filtration-equivalence-audit.log`.
The consumer driver is `audits/RelativeRowsFiltrationEquivalenceAudit.lean`.
Both defining sources and the complete59-origin audit (26 + 33), with all16
consumers, passed warning-free. The fixed59 guard is in the frozen audit
driver for independent confirmation. Source hashes are frozen in
`logs/relative-rows-filtration-equivalence-sources.sha256`. Independent review
passed: fresh two-source rebuild, fixed59 recursive origins and28 strengthened
consumers, all warning-free with unchanged hashes. The independent report is
`docs/REVIEW_20261009_RELATIVE_FILTRATION_PRESENTATION.md`.
