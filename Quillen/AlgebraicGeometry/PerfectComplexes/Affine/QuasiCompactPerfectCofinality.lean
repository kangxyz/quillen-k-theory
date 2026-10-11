/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.KTheory
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedImageRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.JointData

/-! # Original perfect K endpoints on quasi-compact affine opens

Genuine geometric roofs, actual dual weak-arrow approximation and the proved
perfect-complement density identify original relative restriction in every
positive degree. Degree zero is injective with precisely the original
restriction image. The actual source and all canonical maps are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.Affine
open Waldhausen OpenDerivedImage
variable (R : CommRingCat.{u}) (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
include hW

/-- Original relative restriction on a compact affine open is bijective in
all positive degrees, for arbitrary original locally-perfect sheaf complexes. -/
theorem quasiCompact_perfectOpenKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict W.ι (n+1)) := by
  let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
  let : HasBinaryCoproducts (Perfect W.toScheme) := Additivity.hasBinaryCoproducts
    (perfectWaldhausen _)
  exact relativeKRestrict_succ_bijective W.ι
    (affineDenseData R W hW (affine_hasDerivedRoofs R W hW)) (weakArrowJointData W.ι) n

/-- The unchanged original relative restriction is injective also in degree zero. -/
theorem quasiCompact_perfectOpenKRestrict_injective (n : ℕ) :
    Function.Injective (perfectOpenKRestrict W.ι n) := by
  let : Fact (HasDerivedRoofs W.ι) := ⟨affine_hasDerivedRoofs R W hW⟩
  let : HasBinaryCoproducts (Perfect W.toScheme) := Additivity.hasBinaryCoproducts
    (perfectWaldhausen _)
  exact relativeKRestrict_injective W.ι
    (affineDenseData R W hW (affine_hasDerivedRoofs R W hW)) (weakArrowJointData W.ι) n

/-- The actual positive endpoint equivalence has original restriction as forward map. -/
def quasiCompactPerfectOpenKEquiv (n : ℕ) : PerfectOpenK W.ι (n+1) ≃* PerfectK W.toScheme (n+1) :=
  MulEquiv.ofBijective (perfectOpenKRestrict W.ι (n+1))
    (quasiCompact_perfectOpenKRestrict_succ_bijective R W hW n)

@[simp] theorem quasiCompactPerfectOpenKEquiv_toMonoidHom (n : ℕ) :
    (quasiCompactPerfectOpenKEquiv R W hW n :
      PerfectOpenK W.ι (n+1) →* PerfectK W.toScheme (n+1)) =
        perfectOpenKRestrict W.ι (n+1) := rfl

/-- The honest original K-zero endpoint is injective. -/
theorem quasiCompact_perfectOpenKRestrict_zero_injective :
    Function.Injective (perfectOpenKRestrict W.ι 0) :=
  quasiCompact_perfectOpenKRestrict_injective R W hW 0

/-- Its range is precisely the original restriction image from Spec R. -/
theorem quasiCompact_perfectOpenKRestrict_zero_image :
    Function.Injective (perfectOpenKRestrict W.ι 0) ∧
      (perfectOpenKRestrict W.ι 0).range = (perfectKRestrict W.ι 0).range :=
  ⟨quasiCompact_perfectOpenKRestrict_zero_injective R W hW, range_perfectOpenKRestrict_zero W.ι⟩

/-- Original relative K-zero is equivalent to its actual extendible subgroup. -/
def quasiCompactPerfectOpenKZeroImageEquiv : PerfectOpenK W.ι 0 ≃* PerfectOpenKZeroImage W.ι :=
  MulEquiv.ofBijective (perfectOpenKZeroToImage W.ι)
    ⟨fun _ _ h => quasiCompact_perfectOpenKRestrict_zero_injective R W hW (congrArg Subtype.val h),
      perfectOpenKZeroToImage_surjective W.ι⟩

/-- The degree-zero image equivalence retains the exact original endpoint. -/
@[simp] theorem quasiCompactPerfectOpenKZeroImageEquiv_coe (x : PerfectOpenK W.ι 0) :
    (quasiCompactPerfectOpenKZeroImageEquiv R W hW x : PerfectK W.toScheme 0) =
      perfectOpenKRestrict W.ι 0 x := rfl

end Quillen.PerfectComplexes.Affine
