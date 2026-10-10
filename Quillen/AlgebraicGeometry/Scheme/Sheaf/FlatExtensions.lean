/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlatObjectsPullback

/-!
# Genuine flat module-sheaf extensions

A tensor diagram chase proves that a short exact extension of flat modules is
flat. Actual exact module stalks then prove extension closure for stalkwise-flat
module sheaves. This supplies the extension property needed for inherited exact
and Waldhausen structures on flat-complex models; no splitting is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf

/-- Genuine flat modules are closed under arbitrary short exact extensions. -/
theorem moduleFlat_middle_of_shortExact {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    [Module.Flat R S.X₁] [Module.Flat R S.X₃] : Module.Flat R S.X₂ := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro A B _ _ _ _ p hp
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have h₁ := Module.Flat.rTensor_preserves_injective_linearMap (M := S.X₁) p hp
  have h₃ := Module.Flat.rTensor_preserves_injective_linearMap (M := S.X₃) p hp
  have hfB : Function.Injective (S.f.hom.lTensor B) :=
    LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hS.moduleCat_surjective_g
      S.f.hom hS.moduleCat_injective_f he B
  have cf : (S.f.hom.lTensor B).comp (p.rTensor S.X₁) =
      (p.rTensor S.X₂).comp (S.f.hom.lTensor A) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have cg : (S.g.hom.lTensor B).comp (p.rTensor S.X₂) =
      (p.rTensor S.X₃).comp (S.g.hom.lTensor A) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  change (p.rTensor S.X₂) z = 0 at hz
  have hgz : (S.g.hom.lTensor A) z = 0 := by
    apply h₃
    rw [map_zero]
    calc
      _ = (S.g.hom.lTensor B) ((p.rTensor S.X₂) z) := (LinearMap.congr_fun cg z).symm
      _ = 0 := by rw [hz, map_zero]
  obtain ⟨y, hy⟩ := (_root_.lTensor_exact A he hS.moduleCat_surjective_g z).mp hgz
  have hpy : (p.rTensor S.X₁) y = 0 := by
    apply hfB
    rw [map_zero]
    calc
      _ = (p.rTensor S.X₂) ((S.f.hom.lTensor A) y) := LinearMap.congr_fun cf y
      _ = 0 := by rw [hy, hz]
  have hy0 : y = 0 := h₁ (by simpa using hpy)
  simpa [hy0] using hy.symm

/-- Actual module-stalk exactness detects closure of flat sheaves under extensions. -/
theorem stalkwiseFlat_middle_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₁ : stalkwiseFlat X S.X₁) (h₃ : stalkwiseFlat X S.X₃) :
    stalkwiseFlat X S.X₂ := by
  intro x
  let : Module.Flat (X.presheaf.stalk x) (S.map (moduleStalk X x)).X₁ := h₁ x
  let : Module.Flat (X.presheaf.stalk x) (S.map (moduleStalk X x)).X₃ := h₃ x
  exact moduleFlat_middle_of_shortExact (hS.map_of_exact (moduleStalk X x))

end Quillen.SchemeSheaf
