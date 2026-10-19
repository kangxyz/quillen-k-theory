/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# Horizontal isomorphisms in actual two-square routes

Changing either horizontal functor moves its specified isomorphism to the source of
exactly the same pasted route. The left change uses the original second-square naturality.
The intended upstream owner is `Aglib.CategoryTheory.Functor.IsoSquareRouteWhiskering`.
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
  {a a' : A₀ ⥤ A₁} {b b' : A₁ ⥤ A₂} {N : B₀ ⥤ B₁} {M : B₁ ⥤ B₂}
  {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}

/-- A change of the first horizontal functor retains the original second-square naturality. -/
theorem isoSquareRoute_leftIso (r : a ≅ a')
    (s' : a' ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) :
    isoSquareRoute (isoWhiskerRight r E₁ ≪≫ s') t =
      isoWhiskerRight (isoWhiskerRight r b) E₂ ≪≫ isoSquareRoute s' t := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id]
  simpa only [Functor.comp_map, Category.assoc] using
    (congrArg (fun k => k ≫ M.map (s'.hom.app X))
      (t.hom.naturality (r.hom.app X))).symm

/-- A change of the second horizontal functor moves its actual whiskered isomorphism outside. -/
theorem isoSquareRoute_rightIso (r : b ≅ b')
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t' : b' ⋙ E₂ ≅ E₁ ⋙ M) :
    isoSquareRoute s (isoWhiskerRight r E₂ ≪≫ t') =
      isoWhiskerRight (isoWhiskerLeft a r) E₂ ≪≫ isoSquareRoute s t' := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]

end CategoryTheory.Functor
