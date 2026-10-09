# Independent review: internal extension-category sequence

Date: 2026-10-09. Result: **accepted for the frozen two-source structural endpoint**.
No production source was modified. This extends the separately accepted core6
review in `REVIEW_20261009_WALDHAUSEN_EXTENSION_CATEGORY.md`.

## Accepted contract

For every `W : Waldhausen.Structure C`, with independent object/hom universes,
`identityEmbedding W` and `zeroEmbedding W` are the actual functors taking
`A` to `A → A` and `B` to the chosen-zero arrow `0 → B`. Both are proved
Waldhausen-exact. Cofibration preservation uses displayed identity pushouts and
the previously proved choice-independent relative test; pushout preservation
uses the actual componentwise arrow-category universal property. No global
cocompleteness, preadditivity, abelianity, or extra weak-equivalence hypothesis
is needed.

The natural transformations retain the actual components:

- `identityToExtension` has identity source component and the original
  cofibration as target component;
- `extensionToZero` has the canonical map to the chosen zero on sources and
  the actual cofiber projection on targets.

`internalIsCofibrationSequence W` proves the full structural sequence of exact
endofunctors of the extension category:
`(A → A) → (A → B) → (0 → B/A)`.

The relative-cofibration proof is genuine. For a map of extensions from
`A → B` to `A′ → B′`, its displayed internal relative pushout is the actual
extension `A′ → B ⨿[A] A′`. This object is constructed without first assuming
that the map of extensions is Reedy-cofibrant: the required object cofibration
is the pushout leg of the original `A → B`. The comparison to `A′ → B′` has
identity source component and exactly the original relative target map.
The original Reedy hypothesis then proves this comparison is Reedy-cofibrant.
A pushout isomorphism transfers that conclusion to the selected comparison
used by the existing `IsCofibrationTransformation` predicate.

The internal cofiber square is proved componentwise. The source square is an
identity/zero pushout, and the target square is the already proved actual
cofiber square of `A → B`. Full-subcategory reflection yields the genuine
extension-category pushout. The two nontrivial exact endofunctors are proved
exact by composition of the actual source/cofiber projections with the actual
embeddings; the middle functor is literally the identity.

All desired structural assertions are conclusions. No additivity, realized
homotopy, K-equivalence, or desired relative-cofibration condition is smuggled
in as an input.

## Independent verification

I read both sources completely and checked their use of the previously
accepted relative-pushout and cofiber APIs. The two modules were rebuilt from
source into a new isolated overlay. Its six core extension dependencies refer
to the fresh artifacts from the preceding independent core6 rebuild, rather
than the author's six production artifacts. All other unchanged dependencies
are linked. `lean --deps` confirms the fresh `Embeddings` selection.

Compilation used Lean 4.34.0, `-j1`, and the shared slot1 lock, with acquisition
logged. Both sources and the independent audit checked warning-free.

`audits/ExtensionInternalSequenceIndependentAudit.lean` runs a fixed
**50-origin** audit, including every private and generated declaration of the
two modules. Recursive `collectAxioms` permits only `propext`,
`Classical.choice`, and `Quot.sound`. All 50 pass.

Arbitrary-universe consumers check both exact embeddings, the original natural
transformation components, the actual relative comparison components, the
internal cofiber square, and the complete structural sequence. Added
independent consumers check both embedding map formulas, the actual objects
of the displayed relative pushout, its genuine universal square and comparison
identities, the full internal relative condition, and the exact internal
endofunctor types.

Both new source hashes and the preceding six source hashes match after the
run. No implementation changes were required.

## Limits

This accepts the genuine internal sequence of exact endofunctors. It does not
claim a realization/product homeomorphism, an extension-category realization
or K-equivalence, normalized based K-map additivity, or a fibration theorem.
The endofunctors do share the same extension-category object/hom universes,
so there is no cross-universe issue in applying an endofunctor additivity
statement to this particular sequence. Comparisons to the original category
or a product model remain separate.

## Frozen sources and evidence

Manifest: `logs/extension-internal-independent-20261009/sources.sha256`

Manifest SHA-256:
`9e2c28c57a856ea5ba5fd6d4a2bccb404ba61e34560980fced1355a62fcf81a2`

- `Embeddings.lean`: `e4244a2a7d2a43dd79881c8b363f219eeffc49741e0f81e684c178acf55b7caa`
- `InternalSequence.lean`: `086aaa7318923f5703cbad83322d4359831cc5ab8637165d2b345a409fc1f985`

Evidence directory: `logs/extension-internal-independent-20261009/`

- `check.log`: fresh ordered source checks
- `audit.log`: fixed50 recursive origin audit and consumers
- `deps.log`: selected fresh dependency
- `hashes-before.log`, `hashes-after.log`, `core-hashes-after.log`: source rechecks
- `artifacts.sha256`: exact audit, report, logs and new fresh oleans

Independent audit SHA-256:
`ffab3fb0f7660fb2926208b45097c95f38da6f5913f39ed642e24bf9ea1ade64`

Audit log SHA-256:
`b3ea7a244edc6e23d44e9de0514ccb094c1604fb0cdb5ff6b878a5f2977fc71d`
