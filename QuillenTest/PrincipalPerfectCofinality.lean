/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectCofinality
public import Mathlib.Data.ZMod.Basic

/-! # Original all-perfect principal endpoint consumers

These consumers check both original comparison squares, exact positive
forward maps, unique lifts onto the honest K₀ image, the literal homotopy-
fiber boundary criterion, zero localization, and the empty affine case.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.PrincipalPerfectCofinality

open Quillen
open PerfectComplexes PerfectComplexes.Affine

lemma original_endpoint_square {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (perfectOpenKRestrict j n).comp (strictToPerfectOpenKMap j n) =
      (strictToPerfectKMap U n).comp (StrictOpenWeakImage.relativeKRestrict j n) :=
  perfectOpenKRestrict_comp_strictToPerfectOpenKMap j n

lemma original_change_weak_square {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (strictToPerfectOpenKMap j n).comp
      (Waldhausen.KMap (Waldhausen.Fibration.changeWeak_exact (StrictOpenWeakImage.nested j)) n) =
      (perfectOpenKMap j n).comp (strictToPerfectKMap X n) :=
  strictToPerfectOpenKMap_comp_changeWeak j n

lemma original_positive_forward (R : CommRingCat.{u}) (r : R) (n : ℕ) :
    (principalPerfectOpenKEquiv R r n).toMonoidHom =
      perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n+1) := rfl

/-- Membership in the exact original K₀ restriction image is equivalent to
having a unique original relative representative. -/
lemma K0_image_iff_unique_relative_lift (R : CommRingCat.{u}) (r : R)
    (x : PerfectK (Spec (.of (Localization.Away r))) 0) :
    x ∈ (perfectKRestrict (CoherentScheme.principalOpen R r) 0).range ↔
      ∃! a : PerfectOpenK (CoherentScheme.principalOpen R r) 0,
        perfectOpenKRestrict (CoherentScheme.principalOpen R r) 0 a = x := by
  constructor
  · intro hx
    let a := (principalPerfectOpenKZeroImageEquiv R r).symm ⟨x, hx⟩
    have ha : perfectOpenKRestrict (CoherentScheme.principalOpen R r) 0 a = x :=
      congrArg Subtype.val ((principalPerfectOpenKZeroImageEquiv R r).apply_symm_apply ⟨x, hx⟩)
    exact ⟨a, ha, fun b hb => principal_perfectOpenKRestrict_zero_injective R r (hb.trans ha.symm)⟩
  · rintro ⟨a, ha, _⟩
    rw [← range_perfectOpenKRestrict_zero]
    exact ⟨a, ha⟩

/-- The image equivalence retains the original restriction without a
quotient or an abstract replacement of the target subgroup. -/
lemma original_K0_image_value (R : CommRingCat.{u}) (r : R)
    (a : PerfectOpenK (CoherentScheme.principalOpen R r) 0) :
    (principalPerfectOpenKZeroImageEquiv R r a : PerfectK (Spec (.of (Localization.Away r))) 0) =
      perfectOpenKRestrict (CoherentScheme.principalOpen R r) 0 a := rfl

/-- The proved positive endpoint identifies extendibility with vanishing of
the existing original homotopy-fiber boundary. -/
lemma original_boundary_criterion (R : CommRingCat.{u}) (r : R) (n : ℕ)
    (x : PerfectK (Spec (.of (Localization.Away r))) (n+1)) :
    x ∈ (perfectKRestrict (CoherentScheme.principalOpen R r) (n+1)).range ↔
      perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n
        ((principalPerfectOpenKEquiv R r n).symm x) = 1 := by
  change _ ↔ (principalPerfectOpenKEquiv R r n).symm x ∈
    (perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n).ker
  rw [← range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (principalPerfectOpenKEquiv R r n).injective
    exact (DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap
      (CoherentScheme.principalOpen R r) (n+1)) a).trans
      (ha.trans ((principalPerfectOpenKEquiv R r n).apply_symm_apply x).symm)
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    have h := congrArg (principalPerfectOpenKEquiv R r n) ha
    exact (DFunLike.congr_fun (perfectOpenKRestrict_comp_perfectOpenKMap
      (CoherentScheme.principalOpen R r) (n+1)) a).symm.trans
      (h.trans ((principalPerfectOpenKEquiv R r n).apply_symm_apply x))

lemma zero_localization_positive (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict
      (CoherentScheme.principalOpen (.of (ZMod 6)) 0) (n+1)) :=
  principal_perfectOpenKRestrict_succ_bijective _ _ n

lemma empty_affine_original_K0_injective :
    Function.Injective (perfectOpenKRestrict
      (CoherentScheme.principalOpen (.of (ZMod 1)) 0) 0) :=
  principal_perfectOpenKRestrict_zero_injective _ _

end QuillenTest.PrincipalPerfectCofinality
