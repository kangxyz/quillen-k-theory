/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.GlobalRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.GlobalDense
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.KTheory
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.JointData

/-!
# Original qcqs perfect-complex cofinality endpoints

For an original compact open immersion j into a quasi-compact quasi-separated
scheme, the unchanged perfectOpenKRestrict is bijective in positive degrees
and injective in every degree. Degree zero identifies precisely with the
image of the original absolute restriction perfectKRestrict. The displayed
positive and image equivalences retain those exact original forward maps.

Genuine global roofs, actual opposite weak-arrow joint data, dual approximation,
and global perfect-complement density discharge every geometric and structural
input. The public results have no supplied roof, density, or cylinder premise.
No surjectivity onto the full open K-zero group is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes.OpenDerivedImage
open Quillen.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
open Waldhausen OpenDerivedImage
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Original relative restriction on a compact open of a qcqs scheme is bijective in
all positive degrees, for arbitrary original locally-perfect sheaf complexes. -/
theorem qcqs_perfectOpenKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict j (n+1)) := by
  let : Fact (HasDerivedRoofs j) := ⟨qcqs_hasDerivedRoofs j⟩
  let : HasBinaryCoproducts (Perfect U) := Additivity.hasBinaryCoproducts (perfectWaldhausen _)
  exact relativeKRestrict_succ_bijective j
    (globalDenseData j (qcqs_hasDerivedRoofs j)) (weakArrowJointData j) n

/-- The unchanged original relative restriction is injective also in degree zero. -/
theorem qcqs_perfectOpenKRestrict_injective (n : ℕ) :
    Function.Injective (perfectOpenKRestrict j n) := by
  let : Fact (HasDerivedRoofs j) := ⟨qcqs_hasDerivedRoofs j⟩
  let : HasBinaryCoproducts (Perfect U) := Additivity.hasBinaryCoproducts (perfectWaldhausen _)
  exact relativeKRestrict_injective j
    (globalDenseData j (qcqs_hasDerivedRoofs j)) (weakArrowJointData j) n

/-- The actual positive endpoint equivalence has original restriction as forward map. -/
def qcqsPerfectOpenKEquiv (n : ℕ) : PerfectOpenK j (n+1) ≃* PerfectK U (n+1) :=
  MulEquiv.ofBijective (perfectOpenKRestrict j (n+1))
    (qcqs_perfectOpenKRestrict_succ_bijective j n)

@[simp] theorem qcqsPerfectOpenKEquiv_toMonoidHom (n : ℕ) :
    (qcqsPerfectOpenKEquiv j n : PerfectOpenK j (n+1) →* PerfectK U (n+1)) =
      perfectOpenKRestrict j (n+1) := rfl

/-- The honest original K-zero endpoint is injective. -/
theorem qcqs_perfectOpenKRestrict_zero_injective :
    Function.Injective (perfectOpenKRestrict j 0) :=
  qcqs_perfectOpenKRestrict_injective j 0

/-- Its range is precisely the original restriction image from the original global scheme. -/
theorem qcqs_perfectOpenKRestrict_zero_image :
    Function.Injective (perfectOpenKRestrict j 0) ∧
      (perfectOpenKRestrict j 0).range = (perfectKRestrict j 0).range :=
  ⟨qcqs_perfectOpenKRestrict_zero_injective j, range_perfectOpenKRestrict_zero j⟩

/-- Original relative K-zero is equivalent to its actual extendible subgroup. -/
def qcqsPerfectOpenKZeroImageEquiv : PerfectOpenK j 0 ≃* PerfectOpenKZeroImage j :=
  MulEquiv.ofBijective (perfectOpenKZeroToImage j)
    ⟨fun _ _ h => qcqs_perfectOpenKRestrict_zero_injective j (congrArg Subtype.val h),
      perfectOpenKZeroToImage_surjective j⟩

/-- The degree-zero image equivalence retains the exact original endpoint. -/
@[simp] theorem qcqsPerfectOpenKZeroImageEquiv_coe (x : PerfectOpenK j 0) :
    (qcqsPerfectOpenKZeroImageEquiv j x : PerfectK U 0) =
      perfectOpenKRestrict j 0 x := rfl

end Quillen.PerfectComplexes
