/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Conjugating functor composition squares by actual natural isomorphisms

Replacing each functor in a commuting composition square by an explicitly isomorphic functor
preserves the original equality of the two transformation routes. All comparison isomorphisms
remain specified; no new coherence or strictification is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.FunctorConjugation

variable {A B C : Type u} [Category.{v} A] [Category.{v} B] [Category.{v} C]
  {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : A ⥤ C}

/-- Transport the actual composition comparison along the three specified isomorphisms. -/
def compositionIso (c : H ≅ F ⋙ G) (eF : F ≅ F') (eG : G ≅ G') (eH : H ≅ H') :
    H' ≅ F' ⋙ G' :=
  eH.symm ≪≫ c ≪≫ isoWhiskerRight eF G ≪≫ isoWhiskerLeft F' eG

variable {D : Type u} [Category.{v} D]
  {I I' : A ⥤ C} {J J' : B ⥤ D} {K K' : C ⥤ D}

/-- Transport an actual square comparison along all four specified vertex-functor isomorphisms. -/
def squareIso (s : F ⋙ J ≅ I ⋙ K) (eF : F ≅ F') (eJ : J ≅ J')
    (eI : I ≅ I') (eK : K ≅ K') : F' ⋙ J' ≅ I' ⋙ K' :=
  (isoWhiskerLeft F' eJ).symm ≪≫ (isoWhiskerRight eF J).symm ≪≫ s ≪≫
    isoWhiskerRight eI K ≪≫ isoWhiskerLeft I' eK

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type u}
  [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
  [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]
  {F₀₁ F₀₁' : A₀ ⥤ A₁} {F₁₂ F₁₂' : A₁ ⥤ A₂} {F₀₂ F₀₂' : A₀ ⥤ A₂}
  {G₀₁ G₀₁' : B₀ ⥤ B₁} {G₁₂ G₁₂' : B₁ ⥤ B₂} {G₀₂ G₀₂' : B₀ ⥤ B₂}
  {I₀ I₀' : A₀ ⥤ B₀} {I₁ I₁' : A₁ ⥤ B₁} {I₂ I₂' : A₂ ⥤ B₂}
  (cF : F₀₂ ≅ F₀₁ ⋙ F₁₂) (cG : G₀₂ ≅ G₀₁ ⋙ G₁₂)
  (s₀₁ : F₀₁ ⋙ I₁ ≅ I₀ ⋙ G₀₁) (s₁₂ : F₁₂ ⋙ I₂ ≅ I₁ ⋙ G₁₂)
  (s₀₂ : F₀₂ ⋙ I₂ ≅ I₀ ⋙ G₀₂)
  (eF₀₁ : F₀₁ ≅ F₀₁') (eF₁₂ : F₁₂ ≅ F₁₂') (eF₀₂ : F₀₂ ≅ F₀₂')
  (eG₀₁ : G₀₁ ≅ G₀₁') (eG₁₂ : G₁₂ ≅ G₁₂') (eG₀₂ : G₀₂ ≅ G₀₂')
  (eI₀ : I₀ ≅ I₀') (eI₁ : I₁ ≅ I₁') (eI₂ : I₂ ≅ I₂')
  (h : whiskerRight cF.hom I₂ ≫ whiskerLeft F₀₁ s₁₂.hom ≫ whiskerRight s₀₁.hom G₁₂ =
    s₀₂.hom ≫ whiskerLeft I₀ cG.hom)

include h in
/-- The original two-route equation survives conjugation by every specified normalization iso. -/
theorem squareIso_comp :
    whiskerRight (compositionIso cF eF₀₁ eF₁₂ eF₀₂).hom I₂' ≫
      whiskerLeft F₀₁' (squareIso s₁₂ eF₁₂ eI₂ eI₁ eG₁₂).hom ≫
      whiskerRight (squareIso s₀₁ eF₀₁ eI₁ eI₀ eG₀₁).hom G₁₂' =
    (squareIso s₀₂ eF₀₂ eI₂ eI₀ eG₀₂).hom ≫
      whiskerLeft I₀' (compositionIso cG eG₀₁ eG₁₂ eG₀₂).hom := by
  apply NatTrans.ext
  funext X
  simp only [compositionIso, squareIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, isoWhiskerRight_inv, isoWhiskerLeft_inv,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Category.assoc, ← map_comp, NatTrans.naturality_assoc, Iso.hom_inv_id_app_assoc]
  erw [eI₂.inv.naturality_assoc]
  simp only [map_comp, Category.assoc]
  simp only [← map_comp_assoc, Iso.hom_inv_id_app]
  simp only [map_comp, Category.assoc]
  erw [I₂.map_id, Category.id_comp]
  erw [s₁₂.hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [eG₁₂.hom.naturality_assoc]
  have he : G₁₂'.map (I₁.map (eF₀₁.hom.app X)) ≫
      G₁₂'.map (I₁.map (eF₀₁.inv.app X)) = 𝟙 _ := by
    rw [← G₁₂'.map_comp, ← I₁.map_comp, eF₀₁.hom_inv_id_app, I₁.map_id, G₁₂'.map_id]
  rw [← Category.assoc (G₁₂'.map (I₁.map (eF₀₁.hom.app X)))
    (G₁₂'.map (I₁.map (eF₀₁.inv.app X))), he, Category.id_comp]
  simp only [← eG₁₂.hom.naturality_assoc]
  have hc := congrArg (fun η ↦ η.app X) h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app] at hc
  rw [reassoc_of% hc]
  erw [← eG₁₂.hom.naturality]
  rfl

end Quillen.FunctorConjugation
