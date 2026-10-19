/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoPathNormalization
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# Whole-isomorphism normalization of two-square routes

For six categories with independent object and morphism universes, seven specified
functor isomorphisms normalize two adjacent squares and their pasted route. The
intermediate normalization cancels, retaining all associators and the complete original
route without a compatibility premise. The current consumer is whole-isomorphism cube
normalization. The intended upstream owner is
`Aglib.CategoryTheory.Functor.IsoSquareRouteNormalization`.
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
  {a a' : A₀ ⥤ A₁} {b b' : A₁ ⥤ A₂}
  {N N' : B₀ ⥤ B₁} {M M' : B₁ ⥤ B₂}
  {E₀ E₀' : A₀ ⥤ B₀} {E₁ E₁' : A₁ ⥤ B₁} {E₂ E₂' : A₂ ⥤ B₂}

/-- Normalizing all seven functors commutes with the genuine two-square route. -/
theorem isoSquareRoute_faceNormalization
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M)
    (n_a : a ≅ a') (n_b : b ≅ b') (n_N : N ≅ N') (n_M : M ≅ M')
    (e₀ : E₀ ≅ E₀') (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') :
    isoSquareRoute (faceNormalization s n_a e₁ e₀ n_N)
        (faceNormalization t n_b e₂ e₁ n_M) =
      faceNormalization (isoSquareRoute s t) (pathNormalization n_a n_b) e₂ e₀
        (pathNormalization n_N n_M) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, faceNormalization, pathNormalization, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj,
    Category.id_comp, Category.comp_id, Category.assoc]
  rw [← n_M.hom.naturality_assoc, ← M.map_comp_assoc, e₁.hom_inv_id_app, M.map_id,
    Category.id_comp, ← n_M.hom.naturality_assoc, ← n_M.hom.naturality_assoc,
    ← n_M.hom.naturality_assoc, ← n_M.hom.naturality]
  have ht := t.hom.naturality (n_a.inv.app X)
  simp only [Functor.comp_map] at ht
  rw [← Category.assoc (t.hom.app (a'.obj X)) (M.map (E₁.map (n_a.inv.app X))),
    ← ht, Category.assoc]

end CategoryTheory.Functor
