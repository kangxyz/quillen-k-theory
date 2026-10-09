# Dévissage and localization: theorem contracts and dependency audit

Audit date: 2026-10-08. Lean 4.34.0; mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

This records the theorem contracts and original implementation plan. The small-category homotopical dévissage theorem is now formalized in `DevissageHomotopical.lean`; full localization remains in progress.
No Lean declaration or axiom is introduced by this document. Existing project
build results belong in `STATUS.md`; source inspection below does not constitute
new compilation verification.

## Primary mathematical reference

Daniel Quillen, *Higher algebraic K-theory: I*, LNM 341 (1973),
[DOI](https://doi.org/10.1007/BFb0067053),
[accessible original paper](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Quillen-Higher-I.pdf).
The PDF's page numbers differ from its printed pagination.

The classical contracts, in modern notation, are:

- **Dévissage, §5 Theorem 4, PDF page 28.** Let A be essentially small abelian.
  Let B be a nonempty full subcategory closed under subobjects, quotients, and
  finite products. If every M has a finite filtration
  `0 = M₀ ⊆ ⋯ ⊆ Mₙ = M` with `Mᵢ/Mᵢ₋₁ ∈ B`, then the inclusion induces
  `BQ(B) ≃ₕ BQ(A)` and isomorphisms on every nonnegative K-group.
- **Localization, §5 Theorem 5, PDF pages 29–32.** For a Serre subcategory B of
  essentially small abelian A, the quotient q gives a homotopy-fiber sequence
  `BQ(B) → BQ(A) → BQ(A/B)`. Consequently
  `⋯ → Kₙ₊₁(A/B) → Kₙ(B) → Kₙ(A) → Kₙ(A/B) → ⋯`
  ends `K₀(B) → K₀(A) → K₀(A/B) → 0`, naturally for exact functors of pairs.
- **Theorem A, §1, PDF page 9:** contractible comma categories imply a
  classifying-space homotopy equivalence.
- **Theorem B, §1, PDF page 13:** homotopy-equivalence base-change functors on
  comma categories identify their classifying spaces with homotopy fibers.

## Requirements that the Lean statements must preserve

1. Do not assume extension closure in dévissage. With filtration generation,
   extension closure implies every object belongs to B, trivializing its useful
   content. Localization does require extension closure.
2. A full exact abelian embedding alone is not the audited dévissage contract.
   Keep ambient subobject and quotient closure explicit.
3. Filtration length depends on M. No uniform bound, Noetherian hypothesis,
   Artinian hypothesis, or finite-length hypothesis is needed.
4. Use closure up to isomorphism, not dependence on arbitrary chosen kernels,
   cokernels, or representatives. `ObjectProperty` is the natural interface.
5. First implement small categories in compatible universes. An essentially
   small wrapper must transport exact structures and identify resulting
   classifying spaces using actual equivalences. Existing `SmallModel` and
   `equivSmallModel` provide categorical data, not this topological comparison.
6. The homotopy equivalence must have the canonical induced inclusion map as
   its forward map, or a proved compatible pointed homotopy to it. An unrelated
   equivalence between the two spaces does not establish the functorial theorem.
7. The fiber comparison must commute with the projection to `BQ(A)` and use the
   nullhomotopy of `BQ(q) ∘ BQ(i)`. An abstract equivalence of the source and some
   unnamed fiber is insufficient.
8. Maps into the chosen target zero basepoint need the current project's
   rebasing/coherence work. An unbased natural isomorphism does not by itself
   prove equality of based maps on homotopy groups.

## Already present in pinned mathlib

All links in this section are pinned to the audited source commit.

### Abelian full subcategories and filtration ingredients

- [`CategoryTheory/Abelian/Subcategory.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/CategoryTheory/Abelian/Subcategory.lean)
  supplies `Abelian P.FullSubcategory` from `P.ContainsZero`,
  `P.IsClosedUnderKernels`, `P.IsClosedUnderCokernels`, and
  `P.IsClosedUnderFiniteProducts`.
- `CategoryTheory/ObjectProperty/Kernels.lean` derives kernel closure from
  subobject closure and cokernel closure from quotient closure. Its
  `preservesKernels_ι` and `preservesCokernels_ι` provide the inclusion's
  preservation data. Some of these are lemmas, not automatically installed
  instances: construct the exact inclusion deliberately.
- `CategoryTheory/ObjectProperty/ContainsZero.lean` constructs the zero object
  of the full subcategory. `ObjectProperty/FiniteProducts.lean` supplies finite
  product closure machinery.
- `ObjectProperty/Extensions.lean`, `prop_biprod`, gives binary biproduct
  closure from extension closure. Use it, biproduct/product comparison, and
  finite-product closure machinery to equip a Serre subcategory with the
  hypotheses of `Abelian/Subcategory.lean`.
- `CategoryTheory/Filtration/Basic.lean` defines a filtration as a functor to
  `MonoOver M`. This is useful input data, but does not supply finite exhaustive
  filtrations with specified quotient factors or a dévissage theorem.
- `CategoryTheory/Subobject/{Basic,Lattice}.lean` supplies subobjects,
  `Subobject.ofLE`, intersections, sums, and pullback descriptions. The required
  quotient/intersection comparison and Q-comma identifications still need
  dedicated lemmas.

### Serre quotient: substantial existing support

[`CategoryTheory/Abelian/SerreClass/Localization.lean`](https://github.com/leanprover-community/mathlib4/blob/5ed2965256430c3649e86755f9576b54eca72435/Mathlib/CategoryTheory/Abelian/SerreClass/Localization.lean)
contains the needed quotient infrastructure. Do not infer absence from the
stale future-work comments in `SerreClass/Basic.lean` or `MorphismProperty.lean`.

For `P : ObjectProperty A` with `[P.IsSerreClass]`, use
`W := P.isoModSerre`: its arrows have both kernel and cokernel in P.
`W.Localization` and `W.Q` are the constructed category and quotient functor.
Both left and right calculi of fractions, a preadditive quotient, and
additivity of the quotient functor are available.

In namespace `CategoryTheory.ObjectProperty.SerreClassLocalization`, for an
additive localization `L : A ⥤ D` at W with `[Preadditive D]`:

- `abelian L P` equips D with `Abelian D`;
- `preservesFiniteLimits L P` and `preservesFiniteColimits L P` give exactness;
- `isZero_obj_iff L P X` identifies objects killed by L with P;
- `map_eq_zero_iff L P f` identifies arrows killed by L by their image;
- `mono_map_iff`, `epi_map_iff`, and `isIso_map_iff` characterize images of maps;
- `mono_iff` and `epi_iff` give arrow-isomorphism presentations of quotient
  monos/epis by images of ambient monos/epis;
- `whiskeringLeft`, `fullyFaithfulWhiskeringLeft`, and
  `essImage_whiskeringLeft` provide the exact-functor universal property.

This avoids reimplementing Gabriel localization. It does not prove the K-theory
localization theorem. Quotient-subobject lifting, filtered lift categories, and
compatibility with Q still require work.

### Topological primitives

- `AlgebraicTopology/SimplicialSet/Nerve.lean` and `SingularSet.lean`: actual
  nerve, realization, singular set, and their adjunction.
- `AlgebraicTopology/SimplicialSet/TopAdj.lean`: realization of the standard
  simplex, especially `SSet.stdSimplex.toTopObjIsoI`.
- `AlgebraicTopology/SimplicialSet/Homotopy.lean`: simplicial homotopies and a
  conversion to combinatorial simplicial-object homotopies.
- `Topology/Homotopy/Equiv.lean`: actual `ContinuousMap.HomotopyEquiv`.
- `Topology/Homotopy/HomotopyGroup.lean`: actual based homotopy groups,
  loop-space comparisons, groups, and higher-degree commutativity.

## Important audited gaps and false shortcuts

Repository-wide searches and inspection found no reusable Quillen category
Theorem A or B, no topological homotopy-fiber/long-exact-homotopy-sequence API,
and no realization/CW/Whitehead bridge sufficient for these goals.

- `Functor.Final` and `Functor.Initial` in `Limits/Final.lean` require connected
  comma categories, not contractible classifying spaces. They are ordinary
  categorical cofinality and do not imply Theorem A.
- `Algebra/Homology/HomotopyFiber.lean` concerns complexes, not topological
  spaces. Its exact sequences do not establish the desired K-group sequence.
- `TopCat.Homotopy.toSSet` converts topological to simplicial homotopies. It
  goes in the opposite direction from the needed realization lemma.
- `SSet.modelCategoryQuillen` currently provides cofibrations and fibrations.
  `CategoryWithFibrations.lean` explicitly labels the full model structure as
  TODO. The namespace is not evidence that all Kan–Quillen comparison theorems
  are available.
- Acyclicity of a nerve chain complex does not establish its contractibility.
  Likewise a weak homotopy equivalence cannot silently be reported as an actual
  homotopy equivalence. A CW/Whitehead upgrade would itself need proof.
- Categorical connectedness of Q, proved in the project, still needs conversion
  to path-connectedness of its realization for the final zero in the LES.

These are scoped negative audit results for this pin, not claims about future
mathlib versions or the impossibility of another proof strategy.

## Prioritized implementation work

### Stage 1: reusable algebra and exact-functor wrappers

Construct and test the exact full-subcategory inclusion and exact Serre quotient
using the existing abelian exact structure. Prove the induced Q inclusion is
fully faithful. For surjectivity on Q arrows, the apex of an ambient span lies
in B because its monomorphism targets an object of B; representative-isomorphism
invariance must be checked rather than assumed.

Add a small finite-filtration interface. One economical representation is an
order-preserving `s : Fin (n + 1) → Subobject M`, endpoint equalities to bottom
and top, and P-membership of each cokernel of the adjacent `Subobject.ofLE`.
Give transport lemmas and induction on n. Keep this data independent of the
homotopy theorem so the algebra can be compiled and audited immediately.

Acceptance: genuine exact inclusion/quotient constructors, induced Q maps,
zero-kernel identification, and filtration operations; no target-theorem
assumptions in these constructors.

### Stage 2: categorical homotopies realized as topological homotopies

Construct the map associated to a natural transformation and prove its
endpoint equations. The central geometric ingredient is the prism comparison
for realization with the finite interval simplex. Establish precisely the
product comparison needed; do not assume unrestricted preservation of products
by the left adjoint `SSet.toTop`.

Derive classifying-space homotopy equivalences from adjunctions and categorical
equivalences, contractibility from initial/final objects, and compatibility
with basepoint paths. This also serves current K-map coherence work.

Acceptance: actual continuous homotopies with endpoint/basepoint lemmas, then
map-preserving homotopy equivalences. Simplicial naturality alone is not enough.

### Stage 3: Theorem A and dévissage

Prove a realization theorem for the bisimplicial replacement used by Theorem A,
including all required topological hypotheses. A weak-equivalence-first route
is viable only with a separately implemented comparison/upgrading theorem.
State both `StructuredArrow` and `CostructuredArrow` orientations explicitly.

Develop a layer category from pairs of nested subobjects with quotient in P.
Its arrows must match composition of the project's quotient-span Q arrows.
Prove the relevant Q-comma equivalence, the one-filtration-step contraction,
and finite-filtration induction. These are concrete algebraic obligations,
not instances to be assumed by the final theorem.

Acceptance: a proved homotopy equivalence whose forward map is the realized
Q inclusion, followed by group isomorphisms induced by that map. At this stage
dévissage can finish independently of the localization proof.

### Stage 4: actual homotopy fibers and their exact sequence

Implement the fiber of `f : C(X,Y)` over y as the subspace of
`X × C(I,Y)` consisting of `(x,γ)` with `γ(0)=f(x)` and `γ(1)=y`.
This fixed ambient product avoids pretending a dependent family of paths comes
with the right topology automatically. Supply projection, distinguished point,
functorial comparison maps, and a mapping-path fibration model.

Prove the connecting maps on the same cube-based homotopy groups used by the
project. For every adjacent pair, prove image equals kernel; prove naturality
and basepoint compatibility. Treat the `π₁ → π₀` endpoint separately. Prove
path-connectedness of the Q classifying spaces to obtain surjectivity at K₀.

The generic positive homotopy groups are already groups, but commutativity of
K₀ is Q-specific. If claiming the LES in abelian groups, finish the
Grothendieck-group comparison or an independent H-space argument as well.

Acceptance: concrete boundary homomorphisms and exactness proofs; neither an
opaque `FiberSequence` field nor an assumed boundary map counts as localization.

### Stage 5: Theorem B and localization

Prove Theorem B with the fiber construction from Stage 4. Include its
fibered-category specialization and the filtered-category/filtered-diagram
realization results actually used. Filtered categorical colimit lemmas alone
are not homotopy-colimit invariance.

For `F := Q(q)`, construct the functors on `StructuredArrow V F` induced by
all quotient Q arrows. Formalize the auxiliary lift categories and the kernel
comparison functors needed to prove these are homotopy equivalences. Discharge
quotient representative choices using the existing calculus of fractions.
Prove the zero-comma comparison with `Q(B)` and explicitly track the canonical
nullhomotopy from the quotient killing B.

Apply Theorem B only after its hypotheses have been proved for F. Compose the
resulting canonical fiber comparison with Stage 4's exact sequence; check that
the resulting two visible maps agree with the project's exact-functor K maps.
Then prove naturality for exact functors carrying one Serre subcategory into
the other, using the quotient universal property.

Acceptance: canonical fiber comparison, the indexed boundary homomorphisms,
all exactness statements including the K₀ endpoint, and naturality. No theorem
axioms, `sorry`, or structures whose fields assume the desired conclusion.

## Verification discipline

Each stage must compile against the locked dependency set. Add final theorem
constants and their central geometric dependencies to `audits/CentralDeclarationsAudit.lean`.
The final acceptance check is a whole-project build and axiom audit, not merely
successful elaboration of theorem signatures. Keep partially implemented
general topology and completed finite algebra visibly separate in status reports.
