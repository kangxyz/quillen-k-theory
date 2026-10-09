# Independent acceptance: canonical based Waldhausen additivity

Accepted 2026-10-09 06:31 UTC. The original public homomorphisms satisfy
`KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n`
for every natural number n and genuine structural cofibration sequence
F → G → H. The target sum is the actual H ⨿ F functor. This includes K₀,
without assuming commutativity of an arbitrary fundamental group.

The two categories share an object universe u and hom universe v, with u and
v independent. Binary coproducts in the target are structural: the Waldhausen
axioms supply them. No additivity, comparison, fixed-track, or homotopy-group
conclusion is an input.

## Proof checked

The normalized deformation uses actual conjugates of the original pushout
and cofiber endpoint isomorphisms. Independent two-index coherence is proved
componentwise. The actual minimum-cut cylinder and both endpoint families
have strictly constant chosen-zero diagrams, giving three proved relative
realization homotopies. The middle and actual split sequence use the same
normalized separated endpoint.

The relative homotopy is first obtained after the actual subdivision map.
Its forward map is based and induces a proved isomorphism on every positive
homotopy group. Surjectivity cancels precomposition. Neither a based inverse
nor a based inverse homotopy is assumed. The exact diagonal homeomorphism
square then identifies the resulting equality with the original canonical
rebased public KMap homomorphisms.

## Independent evidence

- The nine normalization/mixed-cylinder sources have a separate independent
  review, fresh rebuild and fixed 77-origin recursive audit:
  `REVIEW_20261009_ADDITIVITY_NORMALIZATION_CORE.md`.
- The actual based forward subdivision bridge has a separate independent
  fresh rebuild and fixed 10-origin audit:
  `REVIEW_20261009_SUBDIVISION_BASEPOINT.md`.
- This review fully inspected the two normalized endpoint sources and three
  final homotopy/group-assembly sources. All five were freshly rebuilt into
  `/tmp/quillen-based-final-independent-0626`, with that artifact overlay
  first in LEAN_PATH. No live artifact for these five source origins was used.
- `audits/AdditivityBasedFinalIndependentAudit.lean` recursively checks all
  148 origins across the complete frozen 15-source boundary, including private
  and generated helpers. Only propext, Classical.choice and Quot.sound occur.
- Consumers check the exact public KMap, explicit n=0, actual relative endpoint
  maps, and the genuine bounded-acyclic truncation cofibration sequence.
  Source checks and the final audit are warning-free; before/after hashes match.
- Evidence: `logs/additivity-based-final-independent-{sources.sha256,check.log,
  audit.log,hashes.log,import-path.log}`. Five-source manifest SHA256:
  `12af8ffbe58591e2d0ffac83f5c949860d1a50b24a64c550ae633f79a283575e`.
  Full 15-source manifest: `logs/additivity-based-sources.sha256`.

The accepted theorem does not establish the nested-weak-equivalence fibration,
Gillet–Waldhausen, strict/local-perfect comparison or TT localization.
In particular, isomorphism-model K-theory of bounded or acyclic complexes is
not assumed to vanish or already equal K-theory of the term category.
