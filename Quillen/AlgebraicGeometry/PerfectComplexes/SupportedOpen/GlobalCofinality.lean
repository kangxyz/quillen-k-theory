/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Cofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.JointData
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.KZeroImage

/-!
# Original qcqs supported connective cofinality

For a qcqs scheme X, an original compact open immersion j : U → X, and
compact auxiliary open T, the original relative supported restriction is
bijective in every positive degree and injective in degree zero. The K0
endpoint is exactly the actual global restriction image. Genuine supported
roofs, density, cocylinders and dual approximation discharge every geometric
and categorical premise; forward maps remain literal original restrictions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
open Waldhausen SupportedOpenDerivedImage
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
include hT

/-- Original relative restriction on a compact open of a qcqs scheme is bijective in
all positive degrees, for arbitrary original locally-perfect sheaf complexes. -/
theorem qcqs_perfectSupportedOpenKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n+1)) := by
  let : Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T) :=
    ⟨OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT⟩
  let : HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
  exact relativeKRestrict_succ_bijective j T
    (globalDenseData j T hT (OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT))
      (weakArrowJointData j T) n

/-- The unchanged original relative restriction is injective also in degree zero. -/
theorem qcqs_perfectSupportedOpenKRestrict_injective (n : ℕ) :
    Function.Injective (perfectSupportedOpenKRestrict j T n) := by
  let : Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T) :=
    ⟨OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT⟩
  let : HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
    Additivity.hasBinaryCoproducts (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)
  exact relativeKRestrict_injective j T
    (globalDenseData j T hT (OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT))
      (weakArrowJointData j T) n

/-- The actual positive endpoint equivalence has original restriction as forward map. -/
def qcqsPerfectSupportedOpenKEquiv (n : ℕ) : PerfectSupportedOpenK j T (n+1) ≃* PerfectSupportedK (j
  ⁻¹ᵁ T).ι (n+1) :=
  MulEquiv.ofBijective (perfectSupportedOpenKRestrict j T (n+1))
    (qcqs_perfectSupportedOpenKRestrict_succ_bijective j T hT n)

@[simp] theorem qcqsPerfectSupportedOpenKEquiv_toMonoidHom (n : ℕ) :
    (qcqsPerfectSupportedOpenKEquiv j T hT n :
      PerfectSupportedOpenK j T (n+1) →* PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) =
        perfectSupportedOpenKRestrict j T (n+1) := rfl

/-- The honest original K-zero endpoint is injective. -/
theorem qcqs_perfectSupportedOpenKRestrict_zero_injective :
    Function.Injective (perfectSupportedOpenKRestrict j T 0) :=
  qcqs_perfectSupportedOpenKRestrict_injective j T hT 0

/-- Its range is precisely the original restriction image from the original global scheme. -/
theorem qcqs_perfectSupportedOpenKRestrict_zero_image :
    Function.Injective (perfectSupportedOpenKRestrict j T 0) ∧
      (perfectSupportedOpenKRestrict j T 0).range = (perfectSupportedKRestrict j T 0).range :=
  ⟨qcqs_perfectSupportedOpenKRestrict_zero_injective j T hT,
    range_perfectSupportedOpenKRestrict_zero j T⟩

/-- Original relative K-zero is equivalent to its actual extendible subgroup. -/
def qcqsPerfectSupportedOpenKZeroImageEquiv : PerfectSupportedOpenK j T 0 ≃*
  PerfectSupportedOpenKZeroImage j T :=
  MulEquiv.ofBijective (perfectSupportedOpenKZeroToImage j T)
    ⟨fun _ _ h => qcqs_perfectSupportedOpenKRestrict_zero_injective j T hT (congrArg Subtype.val h),
      perfectSupportedOpenKZeroToImage_surjective j T⟩

/-- The degree-zero image equivalence retains the exact original endpoint. -/
@[simp] theorem qcqsPerfectSupportedOpenKZeroImageEquiv_coe (x : PerfectSupportedOpenK j T 0) :
    (qcqsPerfectSupportedOpenKZeroImageEquiv j T hT x : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) =
      perfectSupportedOpenKRestrict j T 0 x := rfl

end Quillen.PerfectComplexes

end
