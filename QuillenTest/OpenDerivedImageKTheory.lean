/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.KTheory

/-! # Literal image maps, incoming triangles and the sharp K-zero endpoint -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.OpenDerivedImageKTheory
open Quillen.PerfectComplexes.OpenDerivedImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The actual weak-arrow incoming triangle uses the original target projection. -/
theorem original_incoming_triangle
    {Z : WeakArrow.Obj (complexWaldhausen j) (complexCorestrict j)} {B : ComplexObj j}
    (b : B ⟶ (WeakArrow.target (complexWaldhausen j) (complexCorestrict j)).obj Z) :
    ∃ (Y : WeakArrow.Obj (complexWaldhausen j) (complexCorestrict j)) (f : Y ⟶ Z)
      (p : B ⟶ (WeakArrow.target (complexWaldhausen j) (complexCorestrict j)).obj Y),
      (weakArrowOpposite j).cof.unop f ∧ (complexWaldhausen j).weq p ∧
      p.hom ≫ f.hom.right.hom = b.hom := by
  obtain ⟨Y, f, p, hf, hp, he⟩ := weakArrow_target_lift j b
  exact ⟨Y, f, p, hf, hp, congrArg (fun k => k.hom) he⟩

/-- Every original relative K-class follows the unchanged restriction triangle. -/
theorem original_relative_class_triangle (n : ℕ) (x : PerfectOpenK j n) :
    KMap (inclusion_exact j) n (KMap (relativeCorestrict_exact j) n x) =
      perfectOpenKRestrict j n x := DFunLike.congr_fun (relativeKMap_factor j n) x

variable (Jd : Fibration.RowFactorization.JointData (.refl (weakArrowOpposite j)))
include Jd

/-- Original image K-classes have unique original relative lifts in every degree. -/
theorem unique_original_corestriction_preimage (n : ℕ) (y : (complexWaldhausen j).K n) :
    ∃! x : PerfectOpenK j n, KMap (relativeCorestrict_exact j) n x = y := by
  have hb := relativeCorestrict_KMap_bijective j Jd n
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

variable [HasBinaryCoproducts (Perfect U)]
  (hd : Cofinality.DenseCofiberData (perfectWaldhausen U) (objects j))
include hd

/-- Positive target classes have unique lifts along actual relative restriction. -/
theorem unique_original_positive_preimage (n : ℕ) (y : PerfectK U (n+1)) :
    ∃! x : PerfectOpenK j (n+1), perfectOpenKRestrict j (n+1) x = y := by
  have hb := relativeKRestrict_succ_bijective j hd Jd n
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

/-- Degree-zero lifting is exactly membership in the actual original image. -/
theorem original_KZero_unique_iff (y : PerfectK U 0) :
    (∃! x : PerfectOpenK j 0, perfectOpenKRestrict j 0 x = y) ↔ y ∈ (perfectKRestrict j 0).range :=
      by
  constructor
  · rintro ⟨x, rfl, _⟩
    rw [← range_perfectOpenKRestrict_zero j]
    exact ⟨x, rfl⟩
  · intro hy
    let y' : PerfectOpenKZeroImage j := ⟨y, hy⟩
    let x := (relativeKZeroImageEquiv j hd Jd).symm y'
    have hx : perfectOpenKRestrict j 0 x = y := by
      have h := (relativeKZeroImageEquiv j hd Jd).apply_symm_apply y'
      exact congrArg Subtype.val h
    exact ⟨x, hx, fun z hz => relativeKRestrict_injective j hd Jd 0 (hz.trans hx.symm)⟩

/-- The actual relative degree-zero map detects the trivial class. -/
theorem original_relative_KZero_kernel (x : PerfectOpenK j 0) :
    perfectOpenKRestrict j 0 x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply relativeKRestrict_injective j hd Jd 0
    simpa using hx
  · rintro rfl
    exact (perfectOpenKRestrict j 0).map_one

end QuillenTest.OpenDerivedImageKTheory
