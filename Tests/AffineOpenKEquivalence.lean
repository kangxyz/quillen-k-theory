/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenKEquivalence

/-! # Original affine relative-open enhancement consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Waldhausen
universe u
namespace Tests.AffineOpenKEquivalence
variable (R : CommRingCat.{u}) {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Every original relative-perfect class has a unique original strict relative preimage. -/
theorem unique_preimage (n : ℕ) (y : PerfectOpenK j n) :
    ∃! x, strictToPerfectOpenKMap j n x = y := by
  obtain ⟨hi, hs⟩ := Affine.strictToPerfectOpenKMap_bijective R j n
  obtain ⟨x, hx⟩ := hs y
  exact ⟨x, hx, fun z hz => hi (hz.trans hx.symm)⟩

/-- The inverse returns the original strict class, with no positive-degree restriction. -/
theorem inverse_original_forward (n : ℕ)
    (x : (StrictOpenWeakImage.coarseWaldhausen j).K n) :
    (Affine.strictToPerfectOpenKEquiv R j n).symm (strictToPerfectOpenKMap j n x) = x :=
  (Affine.strictToPerfectOpenKEquiv R j n).symm_apply_apply x

/-- The original forward map returns every original perfect relative class. -/
theorem forward_original_inverse (n : ℕ) (y : PerfectOpenK j n) :
    strictToPerfectOpenKMap j n ((Affine.strictToPerfectOpenKEquiv R j n).symm y) = y :=
  (Affine.strictToPerfectOpenKEquiv R j n).apply_symm_apply y

/-- The degree-zero kernel of the actual comparison is trivial. -/
theorem original_zero_kernel (x : (StrictOpenWeakImage.coarseWaldhausen j).K 0)
    (hx : strictToPerfectOpenKMap j 0 x = 1) : x = 1 :=
  (Affine.strictToPerfectOpenKMap_bijective R j 0).1
    (hx.trans (strictToPerfectOpenKMap j 0).map_one.symm)

/-- Actual pullback squares along original deflations stay actual after restriction. -/
theorem original_dual_restriction_pushout {A B D P : (Perfect (Spec R))ᵒᵖ}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {k : D ⟶ P}
    (hi : (perfectOppositeWaldhausen (Spec R)).cof i) (h : IsPushout i f g k) :
    IsPushout ((perfectRestrict j).op.map i) ((perfectRestrict j).op.map f)
      ((perfectRestrict j).op.map g) ((perfectRestrict j).op.map k) :=
  (perfectRestrict_op_exact j).pushout hi h

end Tests.AffineOpenKEquivalence
