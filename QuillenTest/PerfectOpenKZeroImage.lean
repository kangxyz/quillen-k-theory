/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenKZeroImage

/-! # Original relative-open degree-zero image consumers

The tests keep the actual restriction and relative change-of-weak-equivalence
maps. In particular, image membership yields a relative representative,
while an equivalence of the relative endpoint with the image needs precisely
injectivity of the original relative restriction.
-/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.PerfectOpenKZeroImage

open Quillen
open PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original restriction class has its literal change-of-weak representative. -/
theorem original_class_representative (a : PerfectK X 0) :
    (perfectOpenKZeroToImage j (perfectOpenKMap j 0 a) : PerfectK U 0) =
      perfectKRestrict j 0 a :=
  DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) a

/-- Actual membership, rather than a preselected relative point, supplies a representative. -/
theorem image_class_has_relative_representative (x : PerfectK U 0)
    (hx : x ∈ (perfectKRestrict j 0).range) :
    ∃ a : PerfectOpenK j 0, perfectOpenKRestrict j 0 a = x := by
  obtain ⟨a, ha⟩ := perfectOpenKZeroToImage_surjective j ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

/-- Classes outside the original image also remain outside the relative image. -/
theorem no_relative_representative_outside_image (x : PerfectK U 0)
    (hx : x ∉ (perfectKRestrict j 0).range) :
    ¬ ∃ a : PerfectOpenK j 0, perfectOpenKRestrict j 0 a = x := by
  intro h
  exact hx ((range_perfectOpenKRestrict_zero j) ▸ h)

/-- Equality in the honest quotient is exactly equality of actual restrictions. -/
theorem quotient_classes_eq_iff (a b : PerfectOpenK j 0) :
    (QuotientGroup.mk a : PerfectOpenK j 0 ⧸ (perfectOpenKZeroToImage j).ker) =
        QuotientGroup.mk b ↔ perfectOpenKRestrict j 0 a = perfectOpenKRestrict j 0 b := by
  rw [← (perfectOpenKZeroQuotientImageEquiv j).injective.eq_iff, Subtype.ext_iff]
  rfl

/-- The precise remaining input for identifying the endpoint itself with the image. -/
theorem image_map_bijective_iff :
    Function.Bijective (perfectOpenKZeroToImage j) ↔
      Function.Injective (perfectOpenKRestrict j 0) := by
  constructor
  · intro h a b hab
    exact h.injective (Subtype.ext hab)
  · intro h
    exact ⟨fun _ _ hab ↦ h (congrArg Subtype.val hab), perfectOpenKZeroToImage_surjective j⟩

/-- Failure of full restriction surjectivity propagates to the original relative endpoint. -/
theorem relative_not_surjective_of_restriction_not_surjective
    (h : ¬ Function.Surjective (perfectKRestrict j 0)) :
    ¬ Function.Surjective (perfectOpenKRestrict j 0) :=
  fun hs ↦ h ((perfectOpenKRestrict_zero_surjective_iff j).mp hs)

end QuillenTest.PerfectOpenKZeroImage
