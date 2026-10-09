# Generic acyclic-cycle closure

## Endpoint

`Quillen/Waldhausen/GilletWaldhausen/AcyclicCycles.lean` proves actual cycle
closure and actual cycle conflations. The previous 17 split-comparison
sources remain frozen.

For an arbitrary abelian category `A`, an object predicate `P`, and an
actual cochain complex `K : CochainComplex A ℤ`, the assumptions for
`cycles_mem` are exactly:

- `P.IsClosedUnderIsomorphisms`;
- `(abelianExactStructure A).IsKernelClosed P`, the existing structural
  closure condition for kernels of short exact sequences whose middle
  and quotient lie in `P`;
- `∀ n, P (K.X n)`;
- actual acyclicity `K.Acyclic`;
- a strict upper term bound `b`, so `K.X n` is zero when `b < n`.

The conclusion is `∀ n, P (K.cycles n)`. A lower bound is unnecessary.
This theorem does not assume cycle membership, an approximation conclusion,
a K-equivalence, or global projectivity of the chosen objects.

## Actual maps and proof

`cycleSequence K n` is the genuine short complex

`K.cycles n --K.iCycles n--> K.X n --K.toCycles n (n+1)--> K.cycles (n+1)`.

`cycleSequence_shortExact` proves it short exact whenever `K` is exact in
degree `n+1`. The kernel universal property is obtained from the existing
actual cycle kernel, using the factorization of the differential through
the next cycle inclusion. Epimorphism of the second map is proved from
actual exactness in the next degree.

For `cycles_mem`, the cycles at and above the top bound are isomorphic to
the corresponding terms because their outgoing differential has zero
target. Integer downward induction applies the structural kernel-closure
property to each actual cycle sequence.

With the additional standard assumptions needed for the inherited full
exact subcategory (containing zero, extension closure, finite products),
`subcategoryCycleSequence` is an actual short complex in `P.FullSubcategory`.
`subcategoryCycleSequence_conflation` proves that this is a conflation for
`ExactSubcategory.exactStructure (abelianExactStructure A) P`. The lifted
maps retain the original cycle inclusion and differential factorization.

## Literature and next missing steps

This supplies the algebraic cycle-closure step used in the acyclic truncation
argument of Thomason–Trobaugh 1.11.7 and its porism 1.11.8:
https://gwern.net/doc/math/1990-thomason.pdf, PDF pages 31–36.

The genuine Gillet–Waldhausen K-equivalence remains open. In particular,
the library's `ChangeWeakEquivalences` module constructs the comparison
map but does not prove the required fibration theorem, and a genuine
Waldhausen additivity theorem is still missing. The algebraic truncation and exact-functor steps now appear below.
Identification of the one-step quotient with the actual two-term disk
and the K-theoretic additivity/fibration arguments remain separate steps.

No geometric kernel-closure instance is added here. In particular, the
existing locally-noetherian coherent-vector-bundle result is not silently
promoted to an arbitrary-scheme sheaf result, and vector bundles are not
assumed globally projective in the sheaf category.

## Evidence

- Clean focused build: `logs/gillet-waldhausen-cycles-build.log`
- Source hash: `logs/gillet-waldhausen-cycles-checked-sources.sha256`
- Source-origin axiom audit: `audits/GilletWaldhausenCyclesAudit.lean`
- Audit output: `logs/gillet-waldhausen-cycles-axioms.log`

The cycle audit passed all 19 source-origin declarations with only
`propext`, `Classical.choice`, and `Quot.sound`, including generated/private
declarations and an arbitrary-object-universe and arbitrary-hom-universe
consumer of `cycles_mem`.

## Checked acyclic-truncation extension

Three additional sources now compile cleanly and are frozen separately:

- `Quillen/Waldhausen/GilletWaldhausen/BoundedAcyclic.lean`
- `Quillen/Waldhausen/GilletWaldhausen/TruncationMaps.lean`
- `Quillen/Waldhausen/GilletWaldhausen/AcyclicTruncation.lean`

`boundedAcyclic P K` means strict integer term bounds, membership of every
term in `P`, and actual acyclicity. Its isomorphism closure, zero membership,
extension closure and finite-product closure are proved, giving the actual
inherited `boundedAcyclicExactStructure P`.

The existing mathlib functors and cokernel sequence are reused. No alternate
truncation is defined. New component lemmas identify the existing inclusion
at the boundary with the actual cycle inclusion, and show it is an
isomorphism below the boundary. `truncationQuotientBoundaryIso` is obtained
from the actual cokernel universal properties; it identifies the quotient
term in degree `n` with `K.cycles (n+1)`.

`truncLE_mem K n P hK` and `truncationQuotient_mem K n P hK` prove the
subcomplex and actual quotient remain bounded, termwise in `P`, and
acyclic. The strict original bounds are inherited via the degreewise mono
and epi. Boundary membership uses `cycles_mem`; no closure under arbitrary
quotients of `P` is assumed. The quotient is zero below the boundary and
isomorphic to the original terms above it.

`acyclicTruncationSequence K n P hK` retains the original ambient objects
and arrows in the full subcategory.
`acyclicTruncationSequence_conflation` proves it is a genuine conflation
for `boundedAcyclicExactStructure P`.

These first four sources do not assert preservation of conflations by
the truncation functor; that is proved in the later exactness extension
below. Identification of the top quotient with a functorial two-term disk,
additivity, and Gillet–Waldhausen remain separate theorem steps.

Evidence:

- `logs/gillet-waldhausen-truncation-checked-sources.sha256`
- `logs/gillet-waldhausen-truncation-build.log`
- `audits/GilletWaldhausenTruncationAudit.lean`
- `logs/gillet-waldhausen-truncation-axioms.log`
- `logs/gillet-waldhausen-source-token-audit.log`

The combined four-source truncation audit passed all 70 source-origin
declarations, including generated/private declarations and an arbitrary-(u,v)
consumer of the inherited conflation. Only the three standard axioms occur.

## Checked functorial sequence

The fifth source `GilletWaldhausen/TruncationFunctor.lean` assembles the
existing truncation map, the original chain map, and its induced cokernel
map into `truncationSequenceFunctor`. Identity and composition are proved
for all three actual maps.

The restricted `acyclicTruncationSequenceFunctor P n` acts on every chain
map in the bounded acyclic full subcategory. The further
`acyclicTruncationConflationFunctor P n` lands in the actual full category
of inherited conflations. Its composite with the proof-forgetting inclusion
is exactly the same short-complex functor.

All five sources passed the recursive 97-declaration audit, including
private/generated declarations and an arbitrary-(u,v) functor consumer;
only `propext`, `Classical.choice`, and `Quot.sound` occur. Evidence:

- `logs/gillet-waldhausen-truncation-functor-checked-sources.sha256`
- `logs/gillet-waldhausen-truncation-functor-build.log`
- `audits/GilletWaldhausenTruncationFunctorAudit.lean`
- `logs/gillet-waldhausen-truncation-functor-axioms.log`

The initial four modules also passed independent semantic and isolated
Lean review; see `docs/REVIEW_20261009_GW_ACYCLIC_ALGEBRA.md`.

## Checked exact cycle and truncation functors

Two more sources are checked and frozen independently:

- `GilletWaldhausen/CyclesExact.lean`
- `GilletWaldhausen/TruncationExact.lean`

`cyclesMap_epi_of_exactAt` proves the strongest local input used here:
an actual chain map induces an epi on cycles in degree `n` if its preceding
component is epi and only its target is exact at `n`. Consequently,
`cycles_shortExact` takes an ambient short exact sequence and acyclicity
of its rightmost complex only. There is no middle-term acyclicity input.
Additivity of the actual cycle functor is proved by cancellation of cycle
inclusions. `boundedAcyclicCyclesExactFunctor P n` is the resulting genuine
exact functor into the inherited exact full subcategory `P`.

`truncLEEvalIsoBelow` and `truncLEEvalIsoCycles` are actual natural
isomorphisms for the existing truncation functor. The boundary naturality
proof uses the previously checked equality between the actual truncation
inclusion and cycle inclusion. `truncLE_shortExact` proves exactness
degreewise, again assuming acyclicity of only the rightmost complex.
`boundedAcyclicTruncLEExactFunctor P n` packages the actual exact
endofunctor. `boundedAcyclicTruncLEFunctor_eq_first` proves its underlying
functor is exactly the first projection of the frozen truncation sequence.

The hypotheses remain an arbitrary abelian category with independent
object/hom universes, and a replete predicate containing zero, closed under
extensions and kernels of ambient epis between its objects. No exactness
conclusion or equivalence is an input.

Both focused builds are warning-free. The combined seven-source audit
passed all 140 source-origin declarations, including generated/private
declarations and arbitrary-(u,v) exact-functor consumers, with only
`propext`, `Classical.choice`, and `Quot.sound`. Evidence:

- `logs/gillet-waldhausen-exact-checked-sources.sha256`
- `logs/gillet-waldhausen-cycles-exact-build.log`
- `logs/gillet-waldhausen-truncation-exact-build.log`
- `audits/GilletWaldhausenExactAudit.lean`
- `logs/gillet-waldhausen-exact-axioms.log`

The full eight-source cycle/truncation/quotient algebra has now passed
independent semantic and Lean review, with fixed-count origin audits and
actual scheme/map consumers. See
`docs/REVIEW_20261009_GW_QUOTIENT_FUNCTOR.md`. The K-theoretic comparison
remains open.

## Checked exact quotient functor

`GilletWaldhausen/QuotientExact.lean` is checked and frozen separately.
`truncationQuotientBoundaryIso_projection` proves that the boundary
identification respects the actual quotient projection, and
`truncationQuotientBoundaryIso_naturality` derives its naturality by
cancelling that epimorphism. `boundedAcyclicQuotientEvalIsoCycles` packages
the genuine natural isomorphism to the next-cycle functor.

`boundedAcyclicQuotientExactFunctor P n` is the actual third projection
of the frozen truncation sequence, with proved additivity and preservation
of conflations. Degreewise exactness uses the checked exact cycles sequence
at the boundary, the actual quotient projection isomorphism above it,
and zero terms below. The combined eight-source audit passed all 164
source-origin declarations and arbitrary-(u,v) exact-functor and exact
third-projection consumers. Only the three standard axioms occur.

Evidence: `logs/gillet-waldhausen-quotient-exact-checked-sources.sha256`,
`logs/gillet-waldhausen-quotient-exact-build.log`,
`audits/GilletWaldhausenQuotientExactAudit.lean`, and
`logs/gillet-waldhausen-quotient-exact-axioms.log`.

## Checked relative cofibrations and additivity input

`GilletWaldhausen/ExactFunctorSequence.lean` proves a generic structural
result in arbitrary exact categories. For a map of actual conflations,
`relativePushout_inflation` proves its genuine relative-pushout comparison
is an inflation whenever the actual map on quotients is an inflation.
The pushout conflation has the same kernel as the target; the accepted
Q/S pullback calculus identifies the comparison as a pullback of the
quotient inclusion along a deflation. Thus no relative-cofibration
conclusion is assumed. `exactFunctorSequence_isCofibrationSequence` packages
a pointwise conflation sequence of three genuine exact functors into the
structural `Additivity.IsCofibrationSequence` API.

`GilletWaldhausen/TruncationCofibrationSequence.lean` applies this to the
original truncation inclusion and actual cokernel projection. Both
`boundedAcyclicTruncation_isCofibrationSequence` (isomorphism weak
equivalences) and `_quasiIso` (genuine quasi-isomorphisms) are checked.
In particular, for every inherited inflation K→L, the actual comparison
K ⨿[truncLE K] truncLE L → L is an inherited inflation.

These are the structural inputs for additivity; no additivity or
K-equivalence conclusion is claimed here. The combined ten-source audit
passed all 182 declarations with the three standard axioms, including
arbitrary-universe cofibration-sequence consumers and exact unchanged
ambient-arrow checks. Evidence:

- `logs/gillet-waldhausen-cofibration-sequence-checked-sources.sha256`
- `logs/gillet-waldhausen-exact-functor-sequence-build.log`
- `logs/gillet-waldhausen-truncation-cofibration-sequence-build.log`
- `audits/GilletWaldhausenCofibrationSequenceAudit.lean`
- `logs/gillet-waldhausen-cofibration-sequence-axioms.log`

These two adapters and the disk/layer sources below passed independent
semantic review, fresh rebuilds, and the fixed275-origin audit. See
`docs/REVIEW_20261009_GW_DISK_LAYERS.md`.

## Checked actual one-step disk layer

`GilletWaldhausen/IdentityDisk.lean` uses mathlib's `HomologicalComplex.double`
with identity differential in degrees `n,n+1`. It proves actual acyclicity,
strict term bounds, termwise membership, additivity, and preservation of
short exact sequences. `boundedAcyclicDiskExactFunctor P n` does not require
kernel closure of `P`.

`GilletWaldhausen/TruncationLayer.lean` defines `oneStepLayerFunctor P n` as
the actual quotient functor at `n` after the actual `truncLE (n+1)` functor.
Thus its object is precisely
`((K.truncLE (n+1)).shortComplexTruncLE n).X₃`.
The only possible nonzero terms are in degrees `n,n+1`; actual acyclicity
makes their differential invertible. The natural upper-term identification
uses the original quotient projection and the original cycle-boundary iso.
It determines an actual chain isomorphism from the identity disk, and its
naturality is proved on arbitrary chain maps.

`oneStepLayerDiskIso P n` is an actual natural isomorphism in the inherited
bounded-acyclic category from the layer functor to the composite of the
original `(n+1)`-cycle functor and the actual disk functor. The separate
`oneStepLayerExactFunctor` and `oneStepCycleDiskExactFunctor` prove genuine
exactness of both sides. No natural-isomorphism, additivity or K-theory
conclusion is an input.

Both new sources are frozen and independently accepted. The combined
twelve-source audit passed all
275 source-origin declarations, including private/generated declarations,
arbitrary-universe natural-iso/exact-functor consumers, and rfl checks that
the layer is the actual cokernel and the disk is mathlib's actual double.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. Evidence:

- `logs/gillet-waldhausen-layer-checked-sources.sha256`
- `logs/gillet-waldhausen-identity-disk-build.log`
- `logs/gillet-waldhausen-truncation-layer-build.log`
- `audits/GilletWaldhausenLayerAudit.lean`
- `logs/gillet-waldhausen-layer-axioms.log`

The installed mathlib `HasNoLoop` and `Double` sources were unchanged;
their missing artifacts were compiled directly, sequentially under the
same Lean lock, without any Lake build. Their source hashes and empty build
logs are in `logs/gillet-waldhausen-disk-mathlib-sources.sha256`,
`logs/mathlib-has-no-loop-direct-build.log`, and
`logs/mathlib-double-direct-build.log`.

The natural nested-truncation identification, adjacent cofibration
sequence, and fixed-bound endpoints are now proved in the additional
three-source extension below. Genuine K-theoretic additivity and the
change-of-weak-equivalences fibration remain separate work.

## Checked coherence, adjacent sequence, and fixed-bound endpoints

Three further sources are frozen after warning-free focused checks:

- `GilletWaldhausen/TruncationCoherence.lean`
- `GilletWaldhausen/AdjacentTruncation.lean`
- `GilletWaldhausen/FixedBounds.lean`

`truncLECompIso n m h` for `h : n < m` proves the genuine natural
isomorphism from `truncLE n (truncLE m K)` to `truncLE n K`. Its forward
map is exactly the existing truncation map of the original inclusion
`truncLE m K → K`. This statement needs neither acyclicity nor an object
predicate. `truncLECompIso_inclusion` proves exact compatibility with the
original inclusions. The iso is also lifted to bounded acyclic complexes.

`adjacentTruncationInclusion` uses that proved coherence, and
`adjacentTruncationInclusion_ambient` shows that its composite into K is
precisely K's original smaller truncation inclusion. Together with the
actual disk quotient projection this gives the adjacent sequence
`truncLE n → truncLE (n+1) → disk n (cycles (n+1))`.
`adjacentTruncation_isCofibrationSequence` and `_quasiIso` prove the full
structural additivity contract for isomorphism and genuine quasi-isomorphism
weak equivalences. The pointwise conflation and relative-pushout inflation
are both derived.

`fixedAcyclicBounds P a b` is the actual full subcategory of complexes with
these specified strict term bounds. Its zero, isomorphism, and extension
closure are proved; `fixedAcyclicExactStructure P a b` is consequently the
genuine inherited exact structure. Inclusion and every restricted actual
truncation are genuine exact functors. `fixedBoundsTruncLEZeroIso` identifies
the restricted truncation naturally with the actual zero functor whenever
`n<a`. `fixedBoundsTruncLEIdentityIso` identifies it with the original
stratum inclusion whenever `b≤n`, and its forward components are exactly
the original truncation inclusions. No `a≤b` assumption is necessary.

The combined fifteen-source audit passed all 341 origins, including
generated/private declarations, arbitrary-universe exact-stratum and
adjacent-cofibration-sequence consumers, generic ambient coherence, and
both actual endpoint natural isomorphisms. Only the standard three axioms
occur. Prior twelve-source hashes remain unchanged. Evidence:

- `logs/gillet-waldhausen-coherence-checked-sources.sha256`
- `logs/gillet-waldhausen-truncation-coherence-build.log`
- `logs/gillet-waldhausen-adjacent-truncation-build.log`
- `logs/gillet-waldhausen-fixed-bounds-build.log`
- `audits/GilletWaldhausenCoherenceAudit.lean`
- `logs/gillet-waldhausen-coherence-axioms.log`

Independent review of these final three sources passed, including a fresh
rebuild, fixed 341-origin audit, actual-arrow consumers, and frozen hashes;
see `docs/REVIEW_20261009_GW_ADJACENT_FILTRATION.md`. These results
supply actual algebraic filtration data; they do not assert a K-theory
telescoping formula or Gillet–Waldhausen comparison.

## Genuine filtered bounded-stratum coverage

Three additional modules remove a hidden uniform-bound requirement from the
actual diagonal S-construction:

- `BoundedStrata.lean`: the symmetric term-bound predicates `[-N,N]` form
  canonical increasing exact subcategories. Every bounded acyclic complex,
  and every finite family, lies in one actual stage. The finite-family
  coverage theorem does not require closure hypotheses on the term predicate.
  Stage inclusions also reflect inherited inflations: the admissible quotient
  is degreewise an epimorphic image of the bounded target, so its outside terms
  are genuinely zero.
- `BoundedSSet.lean`: restricting the original weak-map predicate by inverse
  image gives actual strictly compatible stage S-maps. Every finite actual
  grid lifts into a common stage, preserving its zeros, inherited inflations,
  actual quotient pushouts, and original weak maps. Stage-to-ambient maps are
  literally injective in each simplicial degree.
- `BoundedSSetColimit.lean`: the universe-compatible natural-number diagram's
  canonical cocone into the original S-set is a proved filtered colimit.
  Only after this concrete universal property is established are the existing
  filtered-realization theorems applied. Every compact-source continuous map
  factors continuously and exactly through one actual bounded stage, also
  above any prescribed bound. Equal maps become literally equal in a larger
  stage, and homotopies relative to compact subsets lift with both original
  endpoint maps retained after the same transition.

The API works for independent ambient object/hom universes and an arbitrary
original weak-map predicate. In particular, it retains genuine quasi-isomorphisms;
for original isomorphisms the restricted weak maps are exactly the bounded
subcategory's isomorphisms. Apart from the ambient abelian category, the
S-set/colimit results require only that the term predicate contains zero and
is replete and extension-closed. Kernel closure, projectivity, a uniform global
bound, and stage-to-ambient equivalences are not inputs.

The principal endpoints are `boundedStratum_covers_finite`,
`boundedStratum_inflation_iff`, `boundedStratumSSetInclusion_surjective`,
`boundedSSetCocone_isColimit`, `boundedSSet_compact_factors`, and
`boundedSSet_homotopyRel_factors`. These establish coverage and compact
factorization, not additivity, contractibility, or Gillet–Waldhausen.

All three focused builds are warning-free. The fixed-count recursive audit
passes all 402 declarations originating in the combined eighteen GW sources,
including private/generated declarations. It also checks independent universes,
closure-free finite-family coverage, actual inflation reflection, retained
isomorphism/quasi-isomorphism classes, exact forward stage maps, the actual
colimit universal property, and compact/relative-homotopy consumers. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. All fifteen earlier
source hashes remain unchanged. Evidence:

- `logs/gillet-waldhausen-bounded-coverage-checked-sources.sha256`
- `logs/gillet-waldhausen-bounded-strata-build.log`
- `logs/gillet-waldhausen-bounded-sset-build.log`
- `logs/gillet-waldhausen-bounded-sset-colimit-build.log`
- `audits/GilletWaldhausenBoundedCoverageAudit.lean`
- `logs/gillet-waldhausen-bounded-coverage-axioms.log`

Independent review of the new bounded-coverage modules passed: fresh four-source
rebuild together with the incidence source, fixed 428-origin audit, actual-map
and compact-relative-homotopy consumers, and matching source hashes. Evidence
is in `logs/gw-coverage-independent-{check,audit,hashes}.log` and
`audits/GilletWaldhausenCoverageIndependentAudit.lean`.

## Actual cycle-to-term incidence sequence

`CycleEvaluationSequence.lean` supplies the genuine exact-functor sequence
`Z_n → E_n → Z_(n+1)` from bounded acyclic termwise-P complexes into the
original inherited term category P. `boundedAcyclicEvaluationFunctor` evaluates
an actual chain map by its original degree-n component; its exactness uses
only actual degreewise short exactness, without kernel closure. Cycle membership
and cycle exactness use the previously proved kernel-closure results.

`boundedAcyclicCycleInclusion` and `boundedAcyclicCycleProjection` retain exactly
the original `iCycles` and `toCycles` maps. Their components are the original
cycle conflations. `boundedAcyclicCycleEvaluation_isCofibrationSequence` derives
the ordinary relative-pushout cofibration condition from exactness of the
next-cycle functor and the accepted generic exact-functor-sequence theorem.
Thus the structural additivity contract is proved with no homotopy or K-theory
conclusion as an input.

These source results allow independent ambient object and hom universes.
Hypotheses are an abelian ambient category and a term predicate containing zero,
replete, extension-closed, and kernel-closed for admissible epimorphisms;
finite-product closure is derived. Evaluation itself needs no kernel closure.
The source and target weak equivalences are isomorphisms. Actual cycles and
terms do not in general carry quasi-isomorphisms to isomorphisms, so there is
no implicit quasi-isomorphism-model version of this incidence statement.

A checked consumer applies the accepted actual unbased additivity theorem to
obtain the original term-evaluation realization map homotopic to the original
sum of the next-cycle and cycle maps. This consumer uses the existing common
object/hom-universe realized S-map interface (`SmallCategory A`). The algebraic
source theorem is not restricted to that common universe. No based K-map
identity, finite-product K-equivalence, Euler-characteristic comparison, or
fibration theorem is claimed here.

The new source rebuild is warning-free. A fixed-count recursive audit passes
all 428 origins across the nineteen GW modules, including actual-map,
minimal-hypothesis, independent-universe, and unbased-additivity consumers.
Only the three standard logical axioms occur; all eighteen earlier source
hashes remain unchanged. Evidence:

- `logs/gillet-waldhausen-cycle-evaluation-checked-sources.sha256`
- `logs/gillet-waldhausen-cycle-evaluation-build.log`
- `audits/GilletWaldhausenCycleEvaluationAudit.lean`
- `logs/gillet-waldhausen-cycle-evaluation-axioms.log`
- `logs/gillet-waldhausen-cycle-evaluation-prior-hashes.log`

Independent review of this new incidence source passed together with the
bounded-coverage modules, including the fixed 428-origin audit. The next algebraic
step toward the all-complexes side is the actual bounded termwise-P category
and its brutal-truncation filtration. Mathlib's existing `stupidTruncFunctor`
should be reused; its natural inclusion and projection are still explicit
TODOs in the installed `Embedding/StupidTrunc.lean` API.

A further checked consumer now applies the actual based-additivity theorem:
`audits/GilletWaldhausenIncidenceBasedAdditivityAudit.lean` proves equality of
the original public normalized term K-map and the original public normalized
sum-functor K-map, in every nonnegative K-degree. Its axiom check finds only
the standard three axioms; the log is
`logs/gillet-waldhausen-incidence-based-additivity-consumer.log`. This consumer
uses no K-map equality as an input. The algebraic incidence source is unchanged;
the parent has now independently accepted the based-additivity infrastructure
as well, across its complete fifteen-source boundary.

## Actual ambient bounded termwise category

Two further sources give the genuine ambient bounded-complex category and
identify its actual acyclic subcategory:

- `BoundedTerms.lean` defines `boundedTerms P K` as actual term boundedness
  together with membership of every actual term in P. Zero/isomorphism and
  extension closure are proved, producing `boundedTermsExactStructure P`.
  Every actual integer shift and actual mapping cone remain in the predicate.
  The shift result needs no closure assumptions on P. Cone closure uses
  repleteness and extension closure, without requiring zero membership.
- `BoundedTermsAcyclic.lean` constructs the original inclusion
  `boundedAcyclicTermsInclusion P`, proves it exact for the inherited exact
  structures and also for genuine quasi-isomorphisms, and proves it reflects
  inherited inflations. For the latter, the actual ambient admissible quotient
  is acyclic by the homology exact sequence, because the source and target
  are acyclic. No arbitrary quotient-closure assumption is inserted.

`boundedTerms_weq_from_zero_iff` characterizes a quasi-isomorphism from any
actual zero object by actual acyclicity of its target.
`boundedTerms_weaklyAcyclic_iff` applies this to the chosen Waldhausen zero,
identifying precisely the original bounded acyclic predicate. The ambient
category results require only an abelian ambient category and P containing
zero, replete and extension-closed; no kernel closure, projectivity, or uniform
bound is assumed. Kernel closure remains a separate hypothesis for cycle
membership and exact cycle functors.

The source and target categories and all inclusion chain maps are the original
ones. The generic bounded-term predicate specializes definitionally to the
accepted strict-perfect predicate on an arbitrary scheme. Actual cone and
shift closure also instantiate the previously proved inherited joint-cylinder
cofibration. These are structural inputs for a future fibration theorem; no
fibration or comparison equivalence is asserted. The isomorphism models of
bounded and acyclic complexes remain distinct nontrivial graded models.

Both focused source builds are warning-free. The fixed-count recursive audit
passes all 455 origins across the twenty-one GW sources, including generated
and private declarations, independent universes, unchanged actual maps,
closure-minimal consumers, actual weak acyclicity, the cylinder input, and the
arbitrary-scheme strict-perfect definitional identification. Only the three
standard logical axioms occur. All nineteen prior frozen source hashes match.
Evidence:

- `logs/gillet-waldhausen-bounded-terms-checked-sources.sha256`
- `logs/gillet-waldhausen-bounded-terms-build.log`
- `logs/gillet-waldhausen-bounded-terms-acyclic-build.log`
- `audits/GilletWaldhausenBoundedTermsAudit.lean`
- `logs/gillet-waldhausen-bounded-terms-axioms.log`
- `logs/gillet-waldhausen-bounded-terms-prior-hashes.log`

The two new sources are independently accepted; see
`docs/REVIEW_20261009_GW_BOUNDED_TERMS.md`. The following brutal
truncation development remains a fresh source boundary.


## Original brutal truncation and adjacent single-term layers

Three further sources are independently accepted:
`StupidTruncationMaps`, `StupidTruncationTransition`, and `StupidTruncationLayer`.
The parent review freshly rebuilt all three, repeated the fixed534 audit and
actual-map consumers, and verified all hashes including the pinned mathlib
source; see `logs/gw-brutal-independent-*` and
`audits/GilletWaldhausenBrutalIndependentAudit.lean`.
For an arbitrary abelian category with independent object and morphism universes,
they retain mathlib's original `stupidTruncFunctor` for the embedding of degrees
at least n. They construct its actual natural inclusion into the original
complex and natural transitions for every n ≤ m, with strict identity and
composition laws. These arrows are degreewise split monomorphisms; a chain
retraction is not asserted.

The adjacent sequence is the actual truncation in degrees at least n+1, then
the actual truncation in degrees at least n, then the original single-term
complex on the original degree-n term. Its original inclusion and projection
are proved short exact, and an actual splitting is given in every degree.
The chosen ambient cokernel is identified with that single-term complex, with
the actual cokernel projection preserved. These raw constructions require no
boundedness, acyclicity, subcategory closure, or projectivity assumptions.

All three focused builds are warning-free. The fixed-count recursive audit
passes all 534 origins across the twenty-four GW sources, including generated
and private declarations, independent-universe consumers, and original-map
compatibility. Only the three standard logical axioms occur. All twenty-one
prior frozen GW hashes match. The pinned mathlib source was unmodified; only
its previously absent `Embedding.StupidTrunc` compiled artifact was built by a
focused direct check.

Evidence:
- `logs/gillet-waldhausen-stupid-truncation-checked-sources.sha256`
- `audits/GilletWaldhausenStupidTruncationAudit.lean`
- `logs/gillet-waldhausen-stupid-truncation-axioms.log`
- `logs/gillet-waldhausen-stupid-truncation-{maps,transition,layer}-build.log`
- `logs/gillet-waldhausen-stupid-truncation-prior-hashes.log`
- `logs/gillet-waldhausen-stupid-trunc-mathlib-sources.sha256`

The bounded-term exact-functor and structural cofibration-sequence wrapper is
being checked separately. This layer concerns isomorphism weak equivalences:
brutal truncation does not in general preserve quasi-isomorphisms.

## Exact bounded-term brutal filtration wrapper

`StupidTruncationExact.lean` is now checked and frozen separately. The original
brutal truncation and original single-term layer preserve actual short exact
sequences, by degreewise retained evaluation isomorphisms and actual zero
terms. Both preserve `boundedTerms P`, yielding genuine inherited exact
functors. Their original adjacent transition and projection form the actual
`boundedTermsStupidLayer_isCofibrationSequence`, including the relative
pushout cofibration property derived from exactness of the quotient functor.
The hypotheses are only an abelian ambient category and P containing zero,
replete, and extension-closed. Kernel closure and projectivity are absent.

The focused build is warning-free. The fixed574-origin recursive audit across
all twenty-five GW sources passes with only the three standard logical
axioms. It includes independent-universe algebraic consumers, unchanged
original functor/map checks, and a canonical normalized `KMap_additivity`
consumer: the actual degree-at-least-n K-map equals the K-map of the actual
sum functor consisting of the degree-n single-term layer and truncation at
n+1. This concerns the isomorphism weak-equivalence model and is not yet an
arithmetic sum formula for K-group homomorphisms. No preservation of
quasi-isomorphisms is claimed for brutal truncation.

Evidence:
- `logs/gillet-waldhausen-stupid-exact-checked-sources.sha256`
- `logs/gillet-waldhausen-stupid-truncation-exact-build.log`
- `audits/GilletWaldhausenStupidExactAudit.lean`
- `logs/gillet-waldhausen-stupid-exact-axioms.log`
- `logs/gillet-waldhausen-stupid-exact-prior-hashes.log`

This wrapper is independently accepted: fresh source rebuild atop the parent
raw-three overlay, the fixed574 audit and original-map/based-additivity
consumers all passed with matching hashes. Evidence is
`logs/gw-brutal-exact-independent-*` and
`audits/GilletWaldhausenBrutalExactIndependentAudit.lean`. Genuine fixed-bound
strata and their actual zero/inclusion endpoint isomorphisms remain next.

## Fixed-term-bound brutal endpoints and their original K-maps

Two further sources, `StupidTruncationFixedBounds` and `StupidTruncationKMap`,
are checked and frozen separately from the accepted twenty-five-source
boundary. `fixedTermsBounds P a b` consists of actual bounded termwise-P
complexes whose terms vanish outside the specified interval. Its inherited
exact structure and the original inclusion and restricted brutal/single-term
exact functors are proved. Increasing the actual interval gives predicate
inclusions. Neither acyclicity nor kernel closure is required.

For n ≤ a, the original restricted brutal functor has a natural isomorphism
to the original stage inclusion. Its forward map is exactly the original
brutal inclusion, proved degreewise invertible. For b < n, the same functor
is genuinely naturally zero. The original normalized K-map therefore equals
the original stage-inclusion K-map at the lower endpoint and the trivial
homomorphism at the upper endpoint. The actual restricted K-map is also
proved equal to the composite of the two original inclusion/truncation
K-maps. All these statements retain independent object/hom universes.
No bound is chosen uniformly on the whole bounded-complex category, and no
quasi-isomorphism preservation is asserted for the brutal functors.

Both focused source checks are warning-free. The fixed608-origin recursive
audit across all twenty-seven GW sources passes with only the three standard
logical axioms, including original-map consumers, closure-minimal endpoint
consumers, all three original K-map identities, and the stronger
independent-universe canonical brutal-additivity consumer. All twenty-five
prior source hashes match.

Evidence:
- `logs/gillet-waldhausen-stupid-fixed-bounds-checked-sources.sha256`
- `audits/GilletWaldhausenStupidFixedBoundsAudit.lean`
- `logs/gillet-waldhausen-stupid-fixed-bounds-axioms.log`
- `logs/gillet-waldhausen-stupid-fixed-bounds-build.log`
- `logs/gillet-waldhausen-stupid-kmap-build.log`
- `logs/gillet-waldhausen-stupid-fixed-bounds-prior-hashes.log`

This two-source endpoint boundary is independently accepted; see
`docs/REVIEW_20261009_GW_FIXED_BRUTAL_ENDPOINTS.md`. The parent freshly
rebuilt both sources and passed the fixed608 audit, including the explicit
K₀ empty-interval case without an a ≤ b or kernel-closure hypothesis. The
ambient bounded-term finite-grid/filtered-colimit coverage and the global
graded K-theory decomposition remain separate obligations.

## Genuine filtered coverage of bounded termwise complexes

`BoundedTermsStrata`, `BoundedTermsSSet`, and `BoundedTermsSSetColimit` are
checked and frozen as a new three-source boundary. They reuse the accepted
generic actual-bound and full-subcategory lemmas. Every finite family of
bounded termwise-P complexes lies in one actual symmetric term-bound stratum.
The canonical increasing inclusions are genuinely exact and reflect
inflations: the actual admissible quotient retains the target's term bounds
by its degreewise epimorphism. No kernel or arbitrary quotient closure is
assumed.

Each actual finite S-grid lifts to such a stage with unchanged zero objects,
cofibrations, genuine pushout squares, and weak maps. Stage weak maps are
exact inverse-image restrictions, encompassing both actual isomorphisms and
actual quasi-isomorphisms. Increasing S-maps are strictly compatible; stage
inclusions are literally injective on simplices. These facts prove the actual
simplicial cocone is a filtered colimit. Only then is the accepted
filtered-realization API applied: compact-source maps factor exactly and
continuously through an actual stage, equal maps become equal at a larger
stage, and relative homotopies lift while retaining their original endpoints.
No categorywide bound or stagewise K-equivalence is an input.

All three focused builds are warning-free. The fixed661-origin recursive
audit across all thirty GW sources passes, with only the three standard
logical axioms. Consumers include independent universes, closure-free finite
coverage, actual inflation reflection and weak predicates, strict original
S-map identities, actual colimit data, and compact/relative-homotopy
factorization. All twenty-seven preceding source hashes match.

Evidence:
- `logs/gillet-waldhausen-bounded-terms-coverage-checked-sources.sha256`
- `audits/GilletWaldhausenBoundedTermsCoverageAudit.lean`
- `logs/gillet-waldhausen-bounded-terms-coverage-axioms.log`
- `logs/gillet-waldhausen-bounded-terms-{strata,sset,colimit}-build.log`
- `logs/gillet-waldhausen-bounded-terms-coverage-prior-hashes.log`

The three sources are independently accepted; see
`docs/REVIEW_20261009_BOUNDED_TERMS_COVERAGE.md`. The independent fresh
rebuild, fixed53 boundary-origin audit, actual-map/compact-relative-homotopy
consumers, and source hashes all passed warning-free. Actual finite termwise
K-decomposition will use the original finite-stratum functors and the now
independently accepted canonical literal sum/product formulas, not an assumed
equivalence.


## Finite termwise K-theory equivalence

The four modules `FiniteTermFiltration`, `FiniteTermEvaluation`,
`FiniteTermKFormula`, and `FiniteTermKEquivalence` are independently accepted.
Their exact contract is in `docs/GILLET_WALDHAUSEN_FINITE_TERMS.md`: the actual
isomorphism-model K-group of the fixed stratum `[a,a+m-1]` is identified with
`Fin m → K(P)`, by the original evaluation K-maps, with inverse the literal
product of original single-insertion K-maps. Empty intervals, K₀, and actual
arbitrary schemes are checked; kernel closure is not assumed.

The final authored fixed772 all34-origin audit, all original-map/inverse
consumers, and the explicitly instantiated scheme consumer pass with only
the three standard logical axioms and no warnings/errors. Independent review
freshly rebuilt all four and checked exactly111 new origins plus strengthened
consumers; all frozen hashes match. See
`docs/REVIEW_20261009_GW_FINITE_TERM_K_EQUIVALENCE.md` and
`logs/gillet-waldhausen-finite-term-k-checked-sources.sha256`.
The complementary finite acyclic-cycle decomposition is a new source boundary.
