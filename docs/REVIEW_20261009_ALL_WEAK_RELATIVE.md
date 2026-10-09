# Independent review: all-weak structure and actual relative-total contractibility

Accepted 2026-10-09 12:22:23 UTC.

## Exact boundary

All three frozen sources were read completely:
`Fibration/AllWeak/Basic`, `CoproductCylinder`, and `RelativeContractible`,
under `Quillen/Waldhausen`. Source manifest:
`logs/all-weak-relative-sources.sha256`.
No production source or live artifact was changed during review.

## Semantic assessment

The all-weak structure retains the original category, cofibrations and chosen
zero; its coarse weak class is literally the top morphism property. Its
Waldhausen, two-out-of-three and extension axioms are proved. The nested
pair retains the original fine weak class, including in actual relative
rows; it does not declare those fine row maps universally weak.

The original unique zero-to-object arrows form the actual natural
transformation. The accepted weak-natural-transformation realization
construction yields its genuine zero-to-identity homotopy. Its zero track
is literally constant. Reversal gives the displayed based contraction of
the actual all-weak S-realization, at the original chosen point.

The coproduct cylinder uses the original source-target coproduct and
projection [f,id]. Its joint arrow is the identity on that coproduct.
Exactness of the actual sum functor followed by the actual identity
embedding proves genuine Reedy exactness, rather than only component
cofibrations. Both endpoint identities use the genuine coproduct maps.
Existence of the required coproducts follows from the Waldhausen structure.
No fine weakness of the cylinder projection is required or claimed.

The accepted original relative-to-coarse equivalence is instantiated with
these proved structural inputs. Its forward map is exactly the original
relative initial-diagonal evaluation. Contractibility of the original
relative total follows through that genuine homotopy equivalence. The
forward equivalence preserves the original relative zero point.

The categorical/all-weak contraction layer retains independent object/hom
universes. The relative realization layer retains its explicit common
universe. The actual bounded-term complex consumer uses its existing
zero/isomorphism/extension closure assumptions and derived finite
biproducts. Contractibility here is not a double-S loop equivalence or the
global homotopy-fiber theorem. No based inverse or based relative-total
contraction is inferred merely from the supplied unbased equivalence.

## Fresh independent validation

A first-path overlay excluded all three target artifact families. Every
source was rebuilt from its exact frozen bytes and every target import
was checked to resolve to a fresh regular olean. The exhaustive recursive
origin audit has the fixed count **44 = 26 + 14 + 4** and permits only the
three standard Lean axioms.

All **31 consumers** pass. The author's23 are retained and eight additions
check the literal top coarse class, the unchanged original fine row-weak
predicate, both actual cylinder endpoint identities, both contraction
endpoints, the canonical changeWeak triangle, and the inverse homotopy
for the prescribed original relative forward map.

All target hashes, **3,834 prerequisite-source**, **17,414 artifact**, and
toolchain/project-pin hashes match before/after. The first independent
source and audit run passed warning-free; no audit or source repair was
needed. The author's earlier missing local finite-biproduct instance was
already corrected before this review and did not change production code.

## Evidence

- Audit: `audits/AllWeakRelativeIndependentAudit.lean`
- Preparation: `logs/prepare-all-weak-relative-independent.py`
- Replay: `logs/verify-all-weak-relative-independent.sh`
- Driver: `logs/all-weak-relative-independent-driver.log`
- Full evidence: `logs/all-weak-relative-independent-20261009/artifacts.sha256`

This is a post12:10-freeze result and is excluded from that archive.
