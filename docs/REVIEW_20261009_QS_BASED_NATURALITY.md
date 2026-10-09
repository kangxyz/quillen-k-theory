# Independent review: normalized based Q/S naturality

2026-10-09. Lean 4.34.0; mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

## Verdict and scope

**Accepted:** the unconditional normalized based naturality theorem and
the exact agreement with the original K-map APIs under their ordinary
structural exactness witness, within the universe scope below. No semantic
or kernel-assumption blocker was found.

The frozen pair under review is:

- `Quillen/Waldhausen/QuillenComparison/ZeroNormalization.lean`
- `Quillen/Waldhausen/QuillenComparison/BasedNaturality.lean`

The source manifest is `logs/qs-based-naturality-sources.sha256`, copied
into this review's evidence directory. Both complete sources and the
relevant basepoint, functoriality, K-map, and comparison dependencies were
inspected. No production source was modified.

The statements use source and target categories in a **common object
universe and common hom universe**, with those two universes independent.
They are not a raw comparison between arbitrary different universe models.
The K-degrees are every `n : ℕ`, on the already-defined shifted homotopy
groups at their specified zero basepoints.

## Exact mathematical contract

For an arbitrary genuine `ExactFunctor EC ED`,
`comparisonKEquiv_naturality` proves that the canonical Q/S comparison
commutes with `normalizedExactSKMap F n` and the existing `F.KMap n`.
No strict-zero assumption or desired naturality square is supplied.

Crucially, `normalizedExactSKMap F n` is defined by the actual based
realization of S-diagram postcomposition with `F.zeroNormalized`. It is
not defined by conjugating the Q-map through the comparison equivalence.
The independent consumer checks this exact forward-map formula by `rfl`.

`normalizedExactSKMap_eq_KMap` identifies that map with the existing
`Waldhausen.KMap hF n`. Here `hF` is the ordinary structural Waldhausen
exactness predicate: preservation of zero objects, cofibrations, weak
equivalences, and arbitrary pushouts along cofibrations. Consequently
`comparisonKEquiv_naturality_KMap` proves the square for the **two original
K-map APIs**. The structural witness contains no K-map, comparison square,
homotopy equivalence, or equivalence conclusion.

The pair does not itself derive this entire structural witness from
Quillen exact-functor data. The separate arbitrary-pushout-preservation
adapter is outside this review. For the unconditional normalized S-map
statement, actual S-diagram preservation already follows from mapped
conflations and their zero-corner cokernel squares, with no extra witness.

## Genuine normalization

`zeroNormalized` uses the existing objectwise rebasing of the original
functor at its chosen zero. `zeroNormalizedIso` is its actual natural
isomorphism with the original functor. Additivity is transported through
that isomorphism, and every actual mapped conflation is transported through
its short-complex component isomorphisms using `ED.iso_closed`. Thus the
normalized object is a genuine exact functor, rather than a functor with
an unproved exactness annotation.

`zeroNormalized_obj_zero` proves literal equality with the target's chosen
zero. The imported `KMap_eq_of_natIso` is genuinely **based**: it lifts the
original natural isomorphism to Q, identifies its normalized zero component
with equality transport, and realizes a homotopy fixed at the actual zero
vertex. Based homotopy invariance of the actual cube-loop quotient then
identifies the original K-maps. An arbitrary unbased homotopy, which would
be insufficient to identify these maps, is not substituted here.

For an already strictly zero-preserving exact functor, uniqueness of maps
into the actual target zero shows its canonical `mapZeroObject` is exactly
`eqToIso h`. The induced Q-isomorphism is likewise equality transport.
`rebaseFunctor_eq_of_eq` therefore identifies the entire normalized Q-functor
with the original Q-functor, and `KMap_eq_piMap_of_zeroEq` identifies the
original K-map with the raw based Q realization map.

## Naturality proof and basepoints

Literal S-diagram postcomposition preserves the constant zero simplex in
every simplicial degree under strict zero preservation. This proves the
actual S basepoint equality and the actual subdivided zero-vertex equality.
The original endpoint naturality square and the original raw Q/S simplicial
naturality square then give strictly commuting based continuous-map squares.
The private `piMap_of_commuting_square` descends these equalities through
the genuine loop quotient; it does not assert an assumed naturality law.

The comparison homomorphism is already characterized by its actual based
subdivision zigzag. Surjectivity of the proved subdivision endpoint
isomorphism cancels that endpoint, giving the strict-zero comparison square.
Applying this to `F.zeroNormalized` and using based Q-map invariance proves
the unconditional normalized square.

For identification with `Waldhausen.KMap`, the two zero-normalizing
isomorphisms are equal because their targets are the same actual zero
object. This gives equality of the underlying rebased functors and hence
of the actual simplicial S-maps. The explicit
`groupsMapOfZeroEq_eq_piMap` eliminates the chosen object equality and
retains the actual based `piMap`. Proof irrelevance handles only proofs
of the same basepoint equality, not a missing path or conjugation.

## Independent verification

Both modules are rebuilt, in dependency order, into a separate olean
overlay. Their original oleans are excluded from that overlay; unchanged
dependency artifacts are linked in. The overlay is first in `LEAN_PATH`
for both the second source check and the independent audit. Import
resolution is logged to confirm selection of the fresh reviewed artifacts.
All compiler invocations use `lean -j1` under
`/tmp/quillen-lean-slot-1.lock`, with explicit acquisition logging.

The audit enumerates every declaration by its actual defining module,
including private/generated declarations, fixes the expected combined
count at 45, and recursively collects axioms allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Independent consumers check:

- actual exactness and the actual natural isomorphism of `zeroNormalized`;
- literal zero preservation and equality with the original Q K-map;
- raw-Q agreement for strictly zero-preserving functors;
- the normalized S-map's exact definition;
- the strict-zero and unconditional comparison squares;
- agreement and naturality with the original Waldhausen K-map API.

Both fresh source builds and every consumer passed without warnings or
errors. All **45 origin declarations** passed the recursive audit: 17 in
`ZeroNormalization` and 28 in `BasedNaturality`. The two source hashes and
all ten inspected-dependency hashes still match. Import-resolution logs
confirm that the fresh normalization olean was used for the second build
and the fresh naturality olean was used for the independent audit.
Evidence directory: `logs/qs-based-naturality-independent-20261009/`.
Audit: `audits/QSBasedNaturalityIndependentAudit.lean`.


SHA256:

```text
bb8ab793219c60eed4930b202366cee224aaf1bf8f14d5eb96d043314a162030  Quillen/Waldhausen/QuillenComparison/ZeroNormalization.lean
13ad0276a86b652b1f31b6b9df73400b2953127afcd53996ecab606ef3cd06cc  Quillen/Waldhausen/QuillenComparison/BasedNaturality.lean
e303a345310763e520f801baf053d035b5f12afabc4852a2776289d8f018191b  logs/qs-based-naturality-independent-20261009/sources.sha256
ab71a7bd55abeb7e827956fe9b06c41837b207653af39c205e75b9af5883a613  audits/QSBasedNaturalityIndependentAudit.lean
064c0c5bad95fb38baa4bb675a7e63bef0e32da4f695c80010f0ac1437457d82  logs/qs-based-naturality-independent-20261009/origin-axioms-and-consumers.log
9a6675f8c296772524a26ae7c632bca668dbb9d58d4f8320758acbdf1a52600e  logs/qs-based-naturality-independent-20261009/import-resolution.log
5645e0fd06bdb8d167619c298eaee5d84f04dbc65ac8c029ea9ac5cdcd74f6f6  logs/qs-based-naturality-independent-20261009/inspected-dependencies.sha256
```

The two source-check logs are empty. The source and dependency rechecks
are in `post-check-hashes.log` and `post-dependency-hashes.log`.
