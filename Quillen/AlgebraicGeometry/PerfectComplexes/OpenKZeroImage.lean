/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The precise original K-zero image of the relative-open endpoint

Relative degree-zero surjectivity and the original restriction factorization
identify its image with the actual image of K-zero restriction from X. The
map to this honest subgroup is surjective; no injectivity or surjectivity
onto all of K-zero of the open is asserted.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The relative endpoint sees exactly the original extendible K-zero subgroup. -/
theorem range_perfectOpenKRestrict_zero :
    (perfectOpenKRestrict j 0).range = (perfectKRestrict j 0).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := perfectOpenKMap_zero_surjective j a
    exact ⟨b, (DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) b).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨perfectOpenKMap j 0 a, DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0)
      a⟩

/-- The honest degree-zero target is the actual subgroup of extendible classes. -/
abbrev PerfectOpenKZeroImage := (perfectKRestrict j 0).range

/-- The original relative restriction, with only its codomain restricted to its actual image. -/
def perfectOpenKZeroToImage : PerfectOpenK j 0 →* PerfectOpenKZeroImage j :=
  (perfectOpenKRestrict j 0).codRestrict (PerfectOpenKZeroImage j)
    (fun a ↦ by
      change perfectOpenKRestrict j 0 a ∈ (perfectKRestrict j 0).range
      rw [← range_perfectOpenKRestrict_zero j]
      exact ⟨a, rfl⟩)

/-- Forgetting subgroup membership recovers the literal original relative restriction. -/
@[simp] theorem perfectOpenKZeroToImage_coe (a : PerfectOpenK j 0) :
    (perfectOpenKZeroToImage j a : PerfectK U 0) = perfectOpenKRestrict j 0 a := rfl

/-- Every class in the honest image has a relative representative. -/
theorem perfectOpenKZeroToImage_surjective : Function.Surjective (perfectOpenKZeroToImage j) := by
  rintro ⟨x, a, rfl⟩
  refine ⟨perfectOpenKMap j 0 a, ?_⟩
  apply Subtype.ext
  exact DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) a

/-- Its kernel is exactly the kernel of the original relative restriction. -/
@[simp] theorem perfectOpenKZeroToImage_ker :
    (perfectOpenKZeroToImage j).ker = (perfectOpenKRestrict j 0).ker := by
  ext a
  change (perfectOpenKZeroToImage j a = 1) ↔ perfectOpenKRestrict j 0 a = 1
  exact Subtype.ext_iff

/-- The always-valid image theorem is a quotient by the actual remaining kernel.
Identifying the relative endpoint itself with this image still requires injectivity. -/
def perfectOpenKZeroQuotientImageEquiv :
    PerfectOpenK j 0 ⧸ (perfectOpenKZeroToImage j).ker ≃* PerfectOpenKZeroImage j :=
  QuotientGroup.quotientKerEquivOfSurjective (perfectOpenKZeroToImage j)
    (perfectOpenKZeroToImage_surjective j)

/-- The image equivalence sends each original relative class to its original restriction. -/
@[simp] theorem perfectOpenKZeroQuotientImageEquiv_mk (a : PerfectOpenK j 0) :
    (perfectOpenKZeroQuotientImageEquiv j (QuotientGroup.mk a) : PerfectK U 0) =
      perfectOpenKRestrict j 0 a := rfl

/-- A surjectivity claim onto all target K-zero is exactly the corresponding
claim for original restriction; the relative factor does not supply it. -/
theorem perfectOpenKRestrict_zero_surjective_iff :
    Function.Surjective (perfectOpenKRestrict j 0) ↔ Function.Surjective (perfectKRestrict j 0) :=
      by
  constructor
  · intro hs y
    obtain ⟨a, ha⟩ := hs y
    obtain ⟨b, hb⟩ := perfectOpenKMap_zero_surjective j a
    refine ⟨b, ?_⟩
    rw [← DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0) b,
      MonoidHom.comp_apply, hb, ha]
  · intro hs y
    obtain ⟨a, rfl⟩ := hs y
    exact ⟨perfectOpenKMap j 0 a, DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap j 0)
      a⟩

end Quillen.PerfectComplexes
