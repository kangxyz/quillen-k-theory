/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasiCompactPerfectCofinality

/-! # Original qc-affine positive endpoint and sharp K-zero image consumers -/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.QuasiCompactPerfectCofinality
open Quillen.PerfectComplexes.Affine

/-- Every original positive target class has one and only one relative lift. -/
theorem original_positive_unique_preimage (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (n : ℕ) (y : PerfectK W.toScheme (n+1)) :
    ∃! x : PerfectOpenK W.ι (n+1), perfectOpenKRestrict W.ι (n+1) x = y := by
  have hb := quasiCompact_perfectOpenKRestrict_succ_bijective R W hW n
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

/-- Original degree-zero lifts exist uniquely exactly on the actual restriction image. -/
theorem original_KZero_unique_iff (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (y : PerfectK W.toScheme 0) :
    (∃! x : PerfectOpenK W.ι 0, perfectOpenKRestrict W.ι 0 x = y) ↔
      y ∈ (perfectKRestrict W.ι 0).range := by
  constructor
  · rintro ⟨x, rfl, _⟩
    rw [← range_perfectOpenKRestrict_zero W.ι]
    exact ⟨x, rfl⟩
  · intro hy
    let y' : PerfectOpenKZeroImage W.ι := ⟨y, hy⟩
    let x := (quasiCompactPerfectOpenKZeroImageEquiv R W hW).symm y'
    have hx : perfectOpenKRestrict W.ι 0 x = y :=
      congrArg Subtype.val ((quasiCompactPerfectOpenKZeroImageEquiv R W hW).apply_symm_apply y')
    exact ⟨x, hx, fun z hz => quasiCompact_perfectOpenKRestrict_zero_injective R W hW (hz.trans
      hx.symm)⟩

/-- The new exact endpoint agrees with the earlier canonical quotient-image map. -/
theorem original_KZero_quotient_comparison (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (x : PerfectOpenK W.ι 0) :
    quasiCompactPerfectOpenKZeroImageEquiv R W hW x =
      perfectOpenKZeroQuotientImageEquiv W.ι (QuotientGroup.mk x) := by
  apply Subtype.ext
  rfl

/-- The inverse equivalence retains original positive restriction exactly. -/
theorem original_positive_inverse (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (n : ℕ) (x : PerfectOpenK W.ι (n+1)) :
    (quasiCompactPerfectOpenKEquiv R W hW n).symm (perfectOpenKRestrict W.ι (n+1) x) = x :=
  (quasiCompactPerfectOpenKEquiv R W hW n).symm_apply_apply x

/-- Empty opens are covered without a nonempty-source or nonzero-ring assumption. -/
theorem empty_open_KZero_injective (R : CommRingCat.{u}) :
    Function.Injective (perfectOpenKRestrict (⊥ : (Spec R).Opens).ι 0) :=
  quasiCompact_perfectOpenKRestrict_zero_injective R ⊥ (by simp)

/-- The actual final endpoint detects the trivial degree-zero class. -/
theorem original_KZero_kernel (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (x : PerfectOpenK W.ι 0) :
    perfectOpenKRestrict W.ι 0 x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    apply quasiCompact_perfectOpenKRestrict_zero_injective R W hW
    simpa using hx
  · rintro rfl
    exact (perfectOpenKRestrict W.ι 0).map_one

end QuillenTest.QuasiCompactPerfectCofinality
