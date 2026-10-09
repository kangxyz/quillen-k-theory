# Genuine Waldhausen extension category

Six frozen implementation sources are listed in
`logs/extension-category-sources.sha256`. The endpoint is
`Quillen.Waldhausen.ExtensionCategory.isCofibrationSequence`.

For any `W : Waldhausen.Structure C`, with independent object universe `u` and
hom universe `v`, `Obj W` is the full category of actual cofibration arrows.
Its objects live in `Type (max u v)` and its homs in `Type v`. No abelian,
additive, smallness, global cocompleteness, or extra realization assumption is
required.

## Actual Waldhausen structure

`waldhausenStructure W` has componentwise weak equivalences. A morphism is a
cofibration exactly when its source component and its actual relative target
pushout map are cofibrations. `cof_relative` and `cof_of_relative` prove this
condition is independent of the chosen pushout witness.

All structural axioms are proved. Relative composition uses the genuine
source-change pushout. A displayed pushout-cube theorem proves the relative map
on a new pushout leg is a cobase change of the original relative map. It follows
that the componentwise pushout arrow remains a cofibration and that the new leg
is a Reedy cofibration. The full arrow-category universal property is constructed
explicitly. Comparing arbitrary pushouts to these actual pointwise pushouts
proves both componentwise preservation and cofibration stability. The gluing
axiom then follows separately on the two components from the original gluing
axiom. The chosen zero is the identity arrow of the genuine chosen zero object.

## Exact functors and structural sequence

- `source W` and `middle W` recover the actual source and target of the original
  cofibration. Their exactness is proved by the componentwise pushout theorem.
- `cofiber W` is the actual categorical pushout of the original arrow along its
  canonical map to the chosen zero object. `quotient W` is the actual pushout
  projection, with a definitional formula through the checked pushout functor.
- `cofiber_exact` proves zero-object, cofibration, weak-equivalence, and pushout
  preservation. It uses the actual source/middle exactness and the structural
  relative-cofibration condition already proved for `inclusion W`.
- `cofiber_isPushout` is the genuine cofiber square, using the original
  cofibration and canonical zero maps.
- `isCofibrationSequence W` proves the full structural
  `Additivity.IsCofibrationSequence` for `source → middle → cofiber`.

The desired cofibration sequence is a theorem, not an assumption. No extension
category K-equivalence, fibration theorem, or Gillet–Waldhausen equivalence is
claimed in this six-source scope. Identity-arrow/zero-arrow embeddings and the
internal extension sequence are a separate subsequent layer.

## Verification

All six exact source files compiled warning-free in a final ordered direct
recheck. The all-origin audit checks 64 declarations, including private/generated
ones, recursively against only `propext`, `Classical.choice`, and `Quot.sound`.
Arbitrary-universe consumers check the actual category sizes, exact Reedy and
weak classes, pointwise pushouts, all three exact functors, the original arrow,
the actual quotient formula, and the genuine structural sequence. The fixed-64
count rerun passed, and all frozen source hashes matched afterward.

Evidence: `audits/ExtensionCategoryAudit.lean`,
`logs/extension-category-audit.log`, and `logs/extension-category-final-*.log`.
