/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StrictPerfectKEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullback
public import Mathlib.Data.ZMod.Basic

/-! # Actual affine K-equivalence consumers

The consumers retain both original public maps, degree zero, inverse and
triangle equations, arbitrary affine pullback, restriction at zero in a
non-domain, and the genuine all-scheme weak-arrow joint factorization.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.AffineStrictPerfectKEquivalence

open Quillen
open PerfectComplexes PerfectComplexes.Affine

lemma actual_strict_forward (R : CommRingCat.{u}) (n : ℕ) :
    (strictToPerfectKEquiv R n).toMonoidHom = strictToPerfectKMap (Spec R) n := rfl

lemma actual_public_forward (R : CommRingCat.{u}) (n : ℕ) :
    (vectorBundleToPerfectKEquiv R n).toMonoidHom = vectorBundleToPerfectKMap (Spec R) n := rfl

/-- Every original perfect K₀ class lifts uniquely along the unchanged
public map from original scheme Q-theory. -/
lemma public_K0_unique_lift (R : CommRingCat.{u}) (x : PerfectK (Spec R) 0) :
    ∃! y : Quillen.Scheme.K (Spec R) 0, vectorBundleToPerfectKMap (Spec R) 0 y = x := by
  obtain ⟨y, hy⟩ := (vectorBundleToPerfectKMap_bijective R 0).surjective x
  exact ⟨y, hy, fun z hz => (vectorBundleToPerfectKMap_bijective R 0).injective (hz.trans hy.symm)⟩

lemma original_strict_inverse (R : CommRingCat.{u}) (n : ℕ) (x : PerfectK (Spec R) n) :
    strictToPerfectKMap (Spec R) n ((strictToPerfectKEquiv R n).symm x) = x :=
  (strictToPerfectKEquiv R n).apply_symm_apply x

/-- Both original comparison maps give the same inverse triangle. -/
lemma original_inverse_triangle (R : CommRingCat.{u}) (n : ℕ) (x : PerfectK (Spec R) n) :
    vectorBundleToStrictKMap (Spec R) n ((vectorBundleToPerfectKEquiv R n).symm x) =
      (strictToPerfectKEquiv R n).symm x := by
  apply (strictToPerfectKMap_bijective R n).injective
  have h := DFunLike.congr_fun (strictToPerfect_comp_vectorBundleToStrictKMap (Spec R) n)
    ((vectorBundleToPerfectKEquiv R n).symm x)
  exact h.trans ((vectorBundleToPerfectKEquiv R n).apply_symm_apply x) |>.trans
    ((strictToPerfectKEquiv R n).apply_symm_apply x).symm

/-- The constructed inverse commutes with original derived K-pullback along
an arbitrary morphism between affine schemes. -/
lemma original_inverse_pullback (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R) (n : ℕ)
    (x : PerfectK (Spec R) n) :
    (strictToPerfectKEquiv S n).symm (perfectKPullback f n x) =
      strictKPullback f n ((strictToPerfectKEquiv R n).symm x) := by
  apply (strictToPerfectKMap_bijective S n).injective
  rw [original_strict_inverse]
  have h := DFunLike.congr_fun (strictToPerfectKMap_pullback f n)
    ((strictToPerfectKEquiv R n).symm x)
  simpa only [MonoidHom.comp_apply, original_strict_inverse] using h

/-- The actual original principal restriction square holds even when the
localization is the zero ring and the starting ring has zero divisors. -/
lemma zero_localization_original_square (n : ℕ) :
    (perfectKRestrict (CoherentScheme.principalOpen (.of (ZMod 6)) 0) n).comp
      (strictToPerfectKEquiv (.of (ZMod 6)) n).toMonoidHom =
    (strictToPerfectKEquiv (.of (Localization.Away (0 : ZMod 6))) n).toMonoidHom.comp
      (strictKRestrict (CoherentScheme.principalOpen (.of (ZMod 6)) 0) n) :=
  strictToPerfectKMap_restrict _ n

/-- Actual joint data works on every scheme, before any affine App2 input. -/
lemma original_joint_factorization (X : Scheme.{u})
    (f : Arrow (Waldhausen.WeakArrow.Obj (perfectWaldhausen X) (strictToPerfect X))ᵒᵖ) :
    (strictToPerfectWeakArrowJointData X).inl.app f ≫
      ((strictToPerfectWeakArrowJointData X).joint.obj f).obj.hom ≫
      (strictToPerfectWeakArrowJointData X).projection.app f = f.hom :=
  (strictToPerfectWeakArrowJointData X).factorization f

lemma empty_spec_original_K0 :
    Function.Bijective (strictToPerfectKMap (Spec (.of (ZMod 1))) 0) :=
  strictToPerfectKMap_bijective _ 0

end QuillenTest.AffineStrictPerfectKEquivalence
