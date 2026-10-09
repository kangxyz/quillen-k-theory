# Internal structural sequence of the extension category

Two new leaf sources are frozen in
`logs/extension-internal-sequence-sources.sha256`; the preceding six-source
extension Waldhausen structure remains unchanged.

`identityEmbedding W` sends `A` to the genuine identity arrow `A → A`.
`zeroEmbedding W` sends `B` to the genuine chosen-zero arrow `0 → B`.
Both functors are proved Waldhausen-exact, including actual pushout preservation.

The natural transformations `identityToExtension` and `extensionToZero` have
exact component formulas:

- `(A → A) → (A → B)` has components `id_A` and the original cofibration;
- `(A → B) → (0 → B/A)` has components the canonical zero map and the actual
  cofiber projection.

`internalIsCofibrationSequence W` proves that these form a genuine structural
cofibration sequence of exact endofunctors of `waldhausenStructure W`.
The pointwise cofiber square is the actual pointwise extension pushout.
For a Reedy cofibration `(A→B) → (A'→B')`, its internal relative pushout is
explicitly the extension `A' → B ⨿[A] A'`. Its comparison to `(A'→B')` has
identity source component and exactly the original relative target map.
Thus the internal relative-cofibration condition is proved from the original
Reedy condition, rather than assumed or replaced by an additivity assertion.

All constructions work for an arbitrary `W : Structure C` with independent
object/hom universes. The internal endofunctors share the same extension-category
object universe, so the existing same-universe functor-additivity theorem can
be applied directly once desired. This layer does not claim an extension-category
realization equivalence, a realization/product homeomorphism, normalized based
K-map additivity, or a fibration theorem.

Focused source rechecks and the recursive origin/exact-consumer audit are in
`logs/extension-internal-final-*.log`,
`logs/extension-internal-sequence-audit.log`, and
`audits/ExtensionInternalSequenceAudit.lean`.

The initial audit checked all 50 declaration origins recursively, permitting only
`propext`, `Classical.choice`, and `Quot.sound`. Both source rechecks were
warning-free; arbitrary-universe consumers retained all exact component formulas.
The fixed-50-count rerun also passed, and both frozen implementation hashes
matched afterward.
