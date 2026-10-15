/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Cofinality.ImageReflection
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.CoverReflection
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalCofinality

/-! # Original K-zero image reflection on a genuine covering pair -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen

/-- The original dense-image inclusion has exactly the original absolute
restriction image on K-zero, through the proved original relative comparison. -/
theorem range_dense_inclusion_eq_restrict_zero {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] [HasBinaryCoproducts (Perfect U)]
    (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j)) :
    (KMap hd.inclusion_exact 0).range = (perfectKRestrict j 0).range := by
  let : Fact (HasDerivedRoofs j) := ⟨qcqs_hasDerivedRoofs j⟩
  rw [← flatten_inclusion_range j hd 0, ← range_perfectOpenKRestrict_zero j,
    ← relativeKMap_factor j 0, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (relativeCorestrict_KMap_bijective j (weakArrowJointData j)
      0).surjective,
    Subgroup.map_top]

variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

include hT hcover in
/-- Original K-zero restriction-image membership is reflected on the overlap.
This uses actual derived gluing and the proved original fine-K-zero obstruction
kernel, rather than an assumed object presentation of K-zero. -/
theorem restrict_mem_range_iff_of_cover (x : PerfectK T.toScheme 0) :
    perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) 0 x ∈
        (perfectKRestrict (j ⁻¹ᵁ T).ι 0).range ↔
      x ∈ (perfectKRestrict T.ι 0).range := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  let : HasBinaryCoproducts (Perfect T.toScheme) := Additivity.hasBinaryCoproducts
    (perfectWaldhausen _)
  let : HasBinaryCoproducts (Perfect (j ⁻¹ᵁ T).toScheme) :=
    Additivity.hasBinaryCoproducts (perfectWaldhausen _)
  let hd := globalDenseData T.ι (qcqs_hasDerivedRoofs T.ι)
  let he := globalDenseData (j ⁻¹ᵁ T).ι (qcqs_hasDerivedRoofs (j ⁻¹ᵁ T).ι)
  rw [← range_dense_inclusion_eq_restrict_zero T.ι hd,
    ← range_dense_inclusion_eq_restrict_zero (j ⁻¹ᵁ T).ι he]
  exact hd.KMap_mem_inclusion_range_iff he
    (perfectRestrict_waldhausenExact (j.resLE T (j ⁻¹ᵁ T) le_rfl))
    (fun A ↦ complexObjects_cover_iff j T hcover A.obj A.property)
    (targetFineJointData _) (targetFineJointData _)
    (targetFineJointData_section _) (targetFineJointData_section _) x

end Quillen.PerfectComplexes.OpenDerivedImage
