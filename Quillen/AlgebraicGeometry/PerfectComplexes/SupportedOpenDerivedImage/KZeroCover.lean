/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.CoverReflection
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionOfLE
public import Quillen.Waldhausen.Cofinality.ImageReflection
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalCofinality

/-! # Genuine supported K-zero image reflection on a covering pair -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen

/-- The actual dense inclusion retains precisely the original supported
restriction image, using the already-proved original relative corestriction. -/
theorem range_dense_inclusion_eq_restrict_zero {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    [HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ Z).ι).FullSubcategory]
    (hd : Cofinality.DenseCofiberData (perfectSupportedWaldhausen (j ⁻¹ᵁ Z).ι) (objects j Z)) :
    (KMap hd.inclusion_exact 0).range = (perfectSupportedKRestrict j Z 0).range := by
  let : Fact (OpenDerivedImage.HasSupportedDerivedRoofs j Z) :=
    ⟨OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j Z hZ⟩
  rw [← flatten_inclusion_range j Z hd 0, ← range_perfectSupportedOpenKRestrict_zero j Z,
    ← relativeKMap_factor j Z 0, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (relativeCorestrict_KMap_bijective j Z (weakArrowJointData j Z)
      0).surjective,
    Subgroup.map_top]

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

omit [IsOpenImmersion j] in
/-- The actual commuting overlap square controls the original auxiliary supports. -/
lemma coverSupport_le :
    (j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z) ≤
      (j.resLE T (j ⁻¹ᵁ T) le_rfl) ⁻¹ᵁ (T.ι ⁻¹ᵁ Z) := by
  intro x hx
  have he := congrArg (fun f : (j ⁻¹ᵁ T).toScheme ⟶ X ↦ f x) (j.resLE_comp_ι (U := T) le_rfl)
  change T.ι ((j.resLE T (j ⁻¹ᵁ T) le_rfl) x) ∈ Z
  change T.ι ((j.resLE T (j ⁻¹ᵁ T) le_rfl) x) = j ((j ⁻¹ᵁ T).ι x) at he
  rw [he]
  exact hx

/-- Literal overlap restriction, with only the support proof normalized by
the original square. No group or chain object is replaced. -/
def overlapKRestrict (n : ℕ) :
    PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι n →*
      PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι n :=
  perfectSupportedKRestrictOfLE (j.resLE T (j ⁻¹ᵁ T) le_rfl)
    ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)) (T.ι ⁻¹ᵁ Z) (coverSupport_le j T Z) n

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (hT : IsCompact (T : Set X)) (hZ : IsCompact (Z : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

include hT hZ hcover in
/-- Actual overlap restriction reflects the original supported K-zero image,
including its prescribed auxiliary support throughout the geometric gluing. -/
theorem restrict_mem_range_iff_of_cover (x : PerfectSupportedK (T.ι ⁻¹ᵁ Z).ι 0) :
    overlapKRestrict j T Z 0 x ∈ (perfectSupportedKRestrict (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) 0).range ↔
      x ∈ (perfectSupportedKRestrict T.ι Z 0).range := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  let : HasBinaryCoproducts (perfectSupported (T.ι ⁻¹ᵁ Z).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen _)
  let : HasBinaryCoproducts (perfectSupported ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen _)
  let hd := globalDenseData T.ι Z hZ (OpenDerivedImage.qcqs_hasSupportedDerivedRoofs T.ι Z hZ)
  let he := globalDenseData (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ)
    (OpenDerivedImage.qcqs_hasSupportedDerivedRoofs (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ))
  rw [← range_dense_inclusion_eq_restrict_zero T.ι Z hZ hd,
    ← range_dense_inclusion_eq_restrict_zero (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) he]
  exact hd.KMap_mem_inclusion_range_iff he
    (perfectSupportedRestrictOfLE_exact (j.resLE T (j ⁻¹ᵁ T) le_rfl) _ _ (coverSupport_le j T Z))
    (fun A ↦ complexObjects_cover_iff j T Z hcover A.obj A.property)
    (targetFineJointData _ _) (targetFineJointData _ _)
    (targetFineJointData_section _ _) (targetFineJointData_section _ _) x

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
