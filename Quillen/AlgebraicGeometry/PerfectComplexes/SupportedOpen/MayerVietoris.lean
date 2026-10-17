/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.KZeroCover
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Excision
public import Quillen.Aglib.Algebra.Group.MayerVietoris
public import Quillen.Waldhausen.Additivity.GroupFormula

/-! # Original two-open Mayer–Vietoris with an auxiliary closed support -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedMayerVietoris
variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

/-- The commutative structure on original supported K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (A : Y.Opens) (n : ℕ) : CommGroup (PerfectSupportedK A.ι n) :=
  Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen A.ι) n

omit [IsOpenImmersion j] in
/-- The literal overlap square, with its original resLE arrow. -/
lemma overlap_square : (j ⁻¹ᵁ T).ι ≫ (supportRestrictionPair j Z).hom.right =
    j.resLE T (j ⁻¹ᵁ T) le_rfl ≫ T.ι :=
  (j.resLE_comp_ι le_rfl).symm

/-- The actual fiber support square induced by the covering square. -/
def fiberPair : supportOpenPair ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange) ⟶
    supportOpenPair (Z ⊔ T.ι.opensRange) :=
  supportedPairUnionSquare (j ⁻¹ᵁ T).ι T.ι (supportRestrictionPair j Z)
    (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z)

omit [IsOpenImmersion j] in
lemma fiberPair_right : (fiberPair j T Z).hom.right = j := rfl

omit [IsOpenImmersion j] in
lemma fiber_support_reverse : j ⁻¹ᵁ (Z ⊔ T.ι.opensRange) ≤
    (j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange := by
  simp only [Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_sup]
  exact le_rfl

variable [CompactSpace X] [CompactSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]

omit [CompactSpace X] [CompactSpace V] in
/-- The induced public target pullback is the literal supported overlap restriction. -/
lemma targetPair_KMap (n : ℕ) :
    perfectSupportedKPullback (qcSupportedBaseSquare
      (supportedPairTargetSquare (j ⁻¹ᵁ T).ι T.ι (supportRestrictionPair j Z)
        (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z))) n =
      SupportedOpenDerivedImage.overlapKRestrict j T Z n := by
  let f := supportedPairTargetSquare (j ⁻¹ᵁ T).ι T.ι (supportRestrictionPair j Z)
    (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z)
  let : IsOpenImmersion f.hom.right :=
    inferInstanceAs (IsOpenImmersion (j.resLE T (j ⁻¹ᵁ T) le_rfl))
  exact perfectSupportedKPullback_eq_restrictOfLE _ _ f n

/-- The genuine supported restriction square in every connective degree. -/
lemma restriction_square (n : ℕ) :
    (SupportedOpenDerivedImage.overlapKRestrict j T Z n).comp
        (perfectSupportedKRestrict T.ι Z n) =
      (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n).comp
        (perfectSupportedKRestrict j Z n) := by
  have h := perfectSupportedKRestrict_pairPullback (j ⁻¹ᵁ T).ι T.ι
    (supportRestrictionPair j Z) (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z) n
  rw [targetPair_KMap] at h
  have hb : perfectSupportedKPullback (qcSupportedBaseSquare (supportRestrictionPair j Z)) n =
      perfectSupportedKRestrict j Z n := (perfectSupportedKRestrict_eq_pullback j Z n).symm
  rw [hb] at h
  exact h

/-- The actual fiber comparison is the existing public supported pair map. -/
def fiberMap (n : ℕ) : PerfectSupportedK (Z ⊔ T.ι.opensRange).ι n →*
    PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange).ι n :=
  perfectSupportedKPullback (qcSupportedBaseSquare (fiberPair j T Z)) n

omit [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme] in
/-- The actual fiber map commutes with original support-forgetting. -/
lemma fiberMap_comp_union (n : ℕ) :
    (perfectSupportedUnionKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n).comp (fiberMap j T Z n) =
      (perfectSupportedKRestrict j Z n).comp (perfectSupportedUnionKMap T.ι Z n) := by
  have h := perfectSupportedUnionKMap_pullback (j ⁻¹ᵁ T).ι T.ι
    (supportRestrictionPair j Z) (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z) n
  have hb : perfectSupportedKPullback (qcSupportedBaseSquare (supportRestrictionPair j Z)) n =
      perfectSupportedKRestrict j Z n := (perfectSupportedKRestrict_eq_pullback j Z n).symm
  rw [hb] at h
  exact h.symm

variable (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

omit [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme] in
include hcover in
/-- Support excision gives bijectivity of the original fiber map, also at K-zero. -/
lemma fiberMap_bijective (n : ℕ) : Function.Bijective (fiberMap j T Z n) := by
  let : IsOpenImmersion (fiberPair j T Z).hom.right := inferInstanceAs (IsOpenImmersion j)
  have he := perfectSupportedKPullback_eq_restrictOfLE _ _ (fiberPair j T Z) n
  change fiberMap j T Z n = _ at he
  rw [he, perfectSupportedKRestrictOfLE_eq_comp]
  apply Function.Bijective.comp (g := perfectSupportedChangeOpenKMap _ n)
    (f := perfectSupportedKRestrict j (Z ⊔ T.ι.opensRange) n)
  · exact perfectSupportedChangeOpenKMap_bijective _ (fiber_support_reverse j T Z) n
  · apply perfectSupportedKRestrict_bijective_of_cover j (Z ⊔ T.ι.opensRange)
    intro x
    rcases hcover x with hx | hx
    · exact Or.inl hx
    · right
      rw [Scheme.Opens.opensRange_ι]
      exact Or.inr hx

/-- The inverse is exactly the inverse of the original support-excision map. -/
def fiberEquiv (n : ℕ) : PerfectSupportedK (Z ⊔ T.ι.opensRange).ι n ≃*
    PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange).ι n :=
  MulEquiv.ofBijective (fiberMap j T Z n) (fiberMap_bijective j T Z hcover n)

end Quillen.PerfectComplexes.SupportedMayerVietoris

end

/-! # Complete original supported connective Mayer–Vietoris exactness -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedMayerVietoris
variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
/-- The commutative structure on original supported K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (A : Y.Opens) (n : ℕ) : CommGroup (PerfectSupportedK A.ι n) :=
  Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen A.ι) n

/-- The two original supported restriction maps, with T first. -/
def restrictionPair (n : ℕ) : PerfectSupportedK Z.ι n →*
    PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι n × PerfectSupportedK (j ⁻¹ᵁ Z).ι n :=
  GroupMayerVietoris.pair (perfectSupportedKRestrict T.ι Z n) (perfectSupportedKRestrict j Z n)

/-- First overlap restriction times inverse second overlap restriction. -/
def overlapDifference (n : ℕ) :
    PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι n × PerfectSupportedK (j ⁻¹ᵁ Z).ι n →*
      PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι n :=
  GroupMayerVietoris.difference (SupportedOpenDerivedImage.overlapKRestrict j T Z n)
    (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n)

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  (hZ : IsCompact (Z : Set X)) (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- Original lower boundary transported through genuine auxiliary-support excision. -/
def lowerBoundary (n : ℕ) : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1) →*
    PerfectSupportedK (Z ⊔ T.ι.opensRange).ι n :=
  (fiberEquiv j T Z hcover n).symm.toMonoidHom.comp
    (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n)

/-- Actual supported Mayer–Vietoris boundary into the unchanged global supported K-group. -/
def connectingHom (n : ℕ) : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1) →*
    PerfectSupportedK Z.ι n :=
  (perfectSupportedUnionKMap T.ι Z n).comp (lowerBoundary j T Z hZ hcover n)

include hZ hcover

/-- The entire original upper boundary is retained by the transported lower one. -/
lemma lowerBoundary_comp_overlap (n : ℕ) :
    (lowerBoundary j T Z hZ hcover n).comp
        (SupportedOpenDerivedImage.overlapKRestrict j T Z (n+1)) =
      qcqsPerfectSupportedConnectingHom T.ι Z hZ n := by
  have h := qcqsPerfectSupportedConnectingHom_pullback (j ⁻¹ᵁ T).ι T.ι
    (supportRestrictionPair j Z) (j.resLE T (j ⁻¹ᵁ T) le_rfl) (overlap_square j T Z)
    (j.isCompact_preimage hZ) hZ n
  rw [targetPair_KMap] at h
  apply MonoidHom.ext
  intro x
  apply (fiberEquiv j T Z hcover n).injective
  change (fiberEquiv j T Z hcover n) ((fiberEquiv j T Z hcover n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun h x).symm

omit [CompactSpace T.toScheme] in
/-- Exactness at the original common support group, also in degree zero. -/
lemma range_lowerBoundary (n : ℕ) :
    (lowerBoundary j T Z hZ hcover n).range =
      ((perfectSupportedKRestrict j Z n).comp (perfectSupportedUnionKMap T.ι Z n)).ker := by
  have hs' (a : PerfectSupportedK (Z ⊔ T.ι.opensRange).ι n) :
      perfectSupportedUnionKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n (fiberMap j T Z n a) =
        perfectSupportedKRestrict j Z n (perfectSupportedUnionKMap T.ι Z n a) :=
    DFunLike.congr_fun (fiberMap_comp_union j T Z n) a
  have he := range_qcqsPerfectSupportedConnectingHom_eq_ker_perfectSupportedUnionKMap
    (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    have hx : qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z)
        (j.isCompact_preimage hZ) n x ∈
        (perfectSupportedUnionKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n).ker :=
      he ▸ (show _ ∈ (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z)
        (j.isCompact_preimage hZ) n).range from ⟨x,rfl⟩)
    change perfectSupportedKRestrict j Z n (perfectSupportedUnionKMap T.ι Z n _) = 1
    rw [← hs']
    change perfectSupportedUnionKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n
      ((fiberEquiv j T Z hcover n) ((fiberEquiv j T Z hcover n).symm _)) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hx
  · intro ha
    have hm : fiberMap j T Z n a ∈
        (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z)
          (j.isCompact_preimage hZ) n).range := by
      rw [he]
      change perfectSupportedUnionKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n (fiberMap j T Z n a) = 1
      rw [hs']
      exact ha
    obtain ⟨x,hx⟩ := hm
    refine ⟨x,?_⟩
    change (fiberEquiv j T Z hcover n).symm
      (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z)
        (j.isCompact_preimage hZ) n x) = a
    rw [hx]
    exact (fiberEquiv j T Z hcover n).symm_apply_apply a

omit [CompactSpace T.toScheme] in
/-- Excision identifies the common support image with the original lower kernel. -/
lemma range_restrict_comp_union (n : ℕ) :
    ((perfectSupportedKRestrict j Z n).comp (perfectSupportedUnionKMap T.ι Z n)).range =
      (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n).ker := by
  rw [← fiberMap_comp_union]
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (fiberMap_bijective j T Z hcover
    n).surjective,
    Subgroup.map_top]
  exact range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict
    (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n

/-- Exactness at the original global supported K-group in every connective degree. -/
lemma range_connectingHom_eq_ker_restrictionPair (n : ℕ) :
    (connectingHom j T Z hZ hcover n).range = (restrictionPair j T Z n).ker :=
  GroupMayerVietoris.range_boundary_eq_ker_pair _ _ _ _
    (range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict T.ι Z hZ n)
    (range_lowerBoundary j T Z hZ hcover n)

omit [CompactSpace T.toScheme] in
/-- The transported lower boundary has the same original positive kernel. -/
lemma range_lower_restrict (n : ℕ) :
    (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (n+1)).range =
      (lowerBoundary j T Z hZ hcover n).ker := by
  rw [range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom
    (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n]
  ext x
  change qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z)
      (j.isCompact_preimage hZ) n x = 1 ↔
    (fiberEquiv j T Z hcover n).symm
      (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n x) = 1
  exact ((fiberEquiv j T Z hcover n).symm.map_eq_one_iff).symm

/-- Exactness at the positive original overlap supported group, with the stated sign. -/
lemma range_overlapDifference_eq_ker_connectingHom (n : ℕ) :
    (overlapDifference j T Z (n+1)).range = (connectingHom j T Z hZ hcover n).ker :=
  GroupMayerVietoris.range_difference_eq_ker_boundary _ _ _ _ _
    (range_qcqsPerfectSupportedConnectingHom_eq_ker_perfectSupportedUnionKMap T.ι Z hZ n)
    (range_lower_restrict j T Z hZ hcover n)
    (lowerBoundary_comp_overlap j T Z hZ hcover n)

/-- Exactness at the pair of positive original supported local groups. -/
lemma range_restrictionPair_eq_ker_overlapDifference (n : ℕ) :
    (restrictionPair j T Z (n+1)).range = (overlapDifference j T Z (n+1)).ker :=
  GroupMayerVietoris.range_pair_eq_ker_difference _ _ _ _ _ _ _
    (range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict T.ι Z hZ (n+1))
    (range_restrict_comp_union j T Z hZ hcover (n+1))
    (range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom T.ι Z hZ n)
    (range_lower_restrict j T Z hZ hcover n)
    (restriction_square j T Z (n+1)) (lowerBoundary_comp_overlap j T Z hZ hcover n)

/-- Genuine supported derived gluing and the original K-zero obstruction give
exactness at the final local pair. No negative boundary is postulated. -/
lemma range_restrictionPair_zero_eq_ker_overlapDifference
    (hT : IsCompact (T : Set X)) :
    (restrictionPair j T Z 0).range = (overlapDifference j T Z 0).ker :=
  GroupMayerVietoris.range_pair_eq_ker_difference_of_image_reflection _ _ _ _ _
    (range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict T.ι Z hZ 0)
    (range_restrict_comp_union j T Z hZ hcover 0)
    (restriction_square j T Z 0)
    (fun x hx ↦ (SupportedOpenDerivedImage.restrict_mem_range_iff_of_cover j T Z hT hZ hcover x).mp
      hx)

end Quillen.PerfectComplexes.SupportedMayerVietoris

end

/-! # Complete supported Mayer–Vietoris on compact covers of qcqs schemes -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedMayerVietoris
/-- The commutative structure on original supported K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (A : Y.Opens) (n : ℕ) : CommGroup (PerfectSupportedK A.ι n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectSupportedWaldhausen A.ι) n
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hT : IsCompact (T : Set X)) (hZ : IsCompact (Z : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- The same original fiber comparison with compactness supplied by the cover data. -/
def qcqsFiberEquiv (n : ℕ) : PerfectSupportedK (Z ⊔ T.ι.opensRange).ι n ≃*
    PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange).ι n := by
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact fiberEquiv j T Z hcover n

/-- The original auxiliary-supported boundary, with every overlap hypothesis discharged. -/
def qcqsConnectingHom (n : ℕ) :
    PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1) →* PerfectSupportedK Z.ι n := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact connectingHom j T Z hZ hcover n

/-- All positive recurring positions retain the original supported restriction maps. -/
theorem qcqs_positiveExactSequence (n : ℕ) :
    (restrictionPair j T Z (n+1)).range = (overlapDifference j T Z (n+1)).ker ∧
    (overlapDifference j T Z (n+1)).range = (qcqsConnectingHom j T Z hT hZ hcover n).ker ∧
    (qcqsConnectingHom j T Z hT hZ hcover n).range = (restrictionPair j T Z n).ker := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact ⟨range_restrictionPair_eq_ker_overlapDifference j T Z hZ hcover n,
    range_overlapDifference_eq_ker_connectingHom j T Z hZ hcover n,
    range_connectingHom_eq_ker_restrictionPair j T Z hZ hcover n⟩

include hT hZ hcover in
/-- Final supported local-pair degree-zero exactness uses genuine supported gluing. -/
theorem qcqs_range_restrictionPair_zero_eq_ker_overlapDifference :
    (restrictionPair j T Z 0).range = (overlapDifference j T Z 0).ker := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact range_restrictionPair_zero_eq_ker_overlapDifference j T Z hZ hcover hT

/-- The complete supported connective tail, including the final local K-zero pair.
This asserts neither surjectivity onto overlap K-zero nor a negative boundary. -/
theorem qcqs_completeZeroTail :
    (overlapDifference j T Z 1).range = (qcqsConnectingHom j T Z hT hZ hcover 0).ker ∧
    (qcqsConnectingHom j T Z hT hZ hcover 0).range = (restrictionPair j T Z 0).ker ∧
    (restrictionPair j T Z 0).range = (overlapDifference j T Z 0).ker :=
  ⟨(qcqs_positiveExactSequence j T Z hT hZ hcover 0).2.1,
    (qcqs_positiveExactSequence j T Z hT hZ hcover 0).2.2,
    qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T Z hT hZ hcover⟩

include hT hZ hcover in
/-- Matching original supported classes glue in every connective degree. -/
theorem qcqs_matching_classes_glue (n : ℕ)
    (x : PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι n) (y : PerfectSupportedK (j ⁻¹ᵁ Z).ι n)
    (hxy : SupportedOpenDerivedImage.overlapKRestrict j T Z n x =
      perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n y) :
    ∃ z : PerfectSupportedK Z.ι n,
      perfectSupportedKRestrict T.ι Z n z = x ∧ perfectSupportedKRestrict j Z n z = y := by
  have he : (restrictionPair j T Z n).range = (overlapDifference j T Z n).ker := by
    cases n with
    | zero => exact qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T Z hT hZ hcover
    | succ n => exact (qcqs_positiveExactSequence j T Z hT hZ hcover n).1
  have hx : (x,y) ∈ (overlapDifference j T Z n).ker :=
    (GroupMayerVietoris.mem_difference_ker _ _ (x,y)).mpr hxy
  rw [← he] at hx
  obtain ⟨z,hz⟩ := hx
  exact ⟨z,congrArg Prod.fst hz,congrArg Prod.snd hz⟩

/-- The entire original relative boundary is recovered before transport into
the original global supported K-group, including the K-one to K-zero case. -/
theorem qcqsConnectingHom_comp_relative (n : ℕ) :
    (qcqsConnectingHom j T Z hT hZ hcover n).comp
      (perfectSupportedOpenKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (n+1)) =
    (perfectSupportedUnionKMap T.ι Z n).comp
      ((qcqsFiberEquiv j T Z hT hcover n).symm.toMonoidHom.comp
        (perfectSupportedOpenConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n)) := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  change ((perfectSupportedUnionKMap T.ι Z n).comp
      ((fiberEquiv j T Z hcover n).symm.toMonoidHom.comp
        (qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n))).comp
      (perfectSupportedOpenKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (n+1)) = _
  rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, qcqsPerfectSupportedConnectingHom_comp_relative]
  rfl

end Quillen.PerfectComplexes.SupportedMayerVietoris

end
