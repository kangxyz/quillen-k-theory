/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Approximation
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Flatten

/-! # Original relative-open endpoint transport through the genuine image -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The two actual image functors factor the unchanged original relative restriction. -/
theorem relativeKMap_factor (n : ℕ) :
    (KMap (inclusion_exact j) n).comp (KMap (relativeCorestrict_exact j) n) =
      perfectOpenKRestrict j n := by
  rw [Quillen.Waldhausen.KMap_comp_KMap]
  rfl

/-- The actual fine perfect cylinder supplies the cofinality data on any scheme. -/
def targetFineJointData (U : Scheme.{u}) : RowFactorization.JointData (.refl (perfectWaldhausen U))
  :=
  complexJointDataOfNested (locallyPerfect U)
    (fun hK hL f => locallyPerfect_mappingCone hK hL f)
    (fun _ hK => locallyPerfect_shift hK 1) (.refl (perfectWaldhausen U))

theorem targetFineJointData_section (U : Scheme.{u}) :
    RowFactorization.SecondEndpointSection (.refl (perfectWaldhausen U)) (targetFineJointData U) :=
  complexJointDataOfNested_secondEndpointSection (locallyPerfect U)
    (fun hK hL f => locallyPerfect_mappingCone hK hL f)
    (fun _ hK => locallyPerfect_shift hK 1) (.refl (perfectWaldhausen U))

/-- The original relative restriction is bijective in positive degrees through
actual corestriction and genuine dense inclusion. -/
theorem relativeKRestrict_succ_bijective [HasBinaryCoproducts (Perfect U)]
    (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j))) (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict j (n+1)) := by
  rw [← relativeKMap_factor j (n+1)]
  exact (inclusion_KMap_succ_bijective j hd (targetFineJointData U) (targetFineJointData_section U)
    n).comp
    (relativeCorestrict_KMap_bijective j Jd (n+1))

/-- The original relative restriction is injective also in degree zero. -/
theorem relativeKRestrict_injective [HasBinaryCoproducts (Perfect U)]
    (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j))) (n : ℕ) :
    Function.Injective (perfectOpenKRestrict j n) := by
  rw [← relativeKMap_factor j n]
  exact (inclusion_KMap_injective j hd (targetFineJointData U) (targetFineJointData_section U)
    n).comp
    (relativeCorestrict_KMap_bijective j Jd n).injective

/-- The exact degree-zero codomain is the original restriction image. -/
def relativeKZeroImageEquiv [HasBinaryCoproducts (Perfect U)]
    (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j))) :
    PerfectOpenK j 0 ≃* PerfectOpenKZeroImage j :=
  MulEquiv.ofBijective (perfectOpenKZeroToImage j)
    ⟨fun _ _ h => relativeKRestrict_injective j hd Jd 0 (congrArg Subtype.val h),
      perfectOpenKZeroToImage_surjective j⟩

/-- Forgetting image membership recovers precisely the original K-zero endpoint. -/
@[simp] theorem relativeKZeroImageEquiv_coe [HasBinaryCoproducts (Perfect U)]
    (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j))) (x : PerfectOpenK j 0) :
    (relativeKZeroImageEquiv j hd Jd x : PerfectK U 0) = perfectOpenKRestrict j 0 x := rfl

end Quillen.PerfectComplexes.OpenDerivedImage
