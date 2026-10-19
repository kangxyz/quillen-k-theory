/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation
public import Mathlib.CategoryTheory.EqToHom

/-!
# Composition coherence after conjugating evaluation squares

Replacing three evaluation functors by specified isomorphic functors preserves the
original composition equation. The source functor equality and the target composition
isomorphism remain unchanged. All six categories have independent universes.
The intended upstream owner is `Aglib.CategoryTheory.Functor.IsoSquareConjugateComposition`.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
namespace CategoryTheory.Functor

variable {A₀ : Type u₀} [Category.{v₀} A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {B₀ : Type w₀} [Category.{z₀} B₀]
  {B₁ : Type w₁} [Category.{z₁} B₁] {B₂ : Type w₂} [Category.{z₂} B₂]

/-- Original composition pasting is preserved by all three actual evaluation normalizations. -/
theorem isoSquareConjugate_comp_app
    (Sf : A₀ ⥤ A₁) (Sg : A₁ ⥤ A₂) (Sfg : A₀ ⥤ A₂) (hS : Sfg = Sf ⋙ Sg)
    (Pf : B₀ ⥤ B₁) (Pg : B₁ ⥤ B₂) (Pfg : B₀ ⥤ B₂)
    {U₀ E₀ : A₀ ⥤ B₀} {U₁ E₁ : A₁ ⥤ B₁} {U₂ E₂ : A₂ ⥤ B₂}
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (z₀ : U₀ ≅ E₀) (z₁ : U₁ ≅ E₁) (z₂ : U₂ ≅ E₂)
    (h : ∀ x, κfg.hom.app x ≫ β.hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
        κg.hom.app (Sf.obj x) ≫ Pg.map (κf.hom.app x)) :
    ∀ x, (isoSquareConjugate κfg z₀ z₂).hom.app x ≫ β.hom.app (E₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ E₂) hS)).app x ≫
        (isoSquareConjugate κg z₁ z₂).hom.app (Sf.obj x) ≫
          Pg.map ((isoSquareConjugate κf z₀ z₁).hom.app x) := by
  subst Sfg
  intro x
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at h ⊢
  simp only [isoSquareConjugate, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← Pg.map_comp_assoc, Iso.hom_inv_id_app, Pg.map_id, Category.id_comp]
  rw [β.hom.naturality, reassoc_of% h x]
  rfl

end CategoryTheory.Functor
