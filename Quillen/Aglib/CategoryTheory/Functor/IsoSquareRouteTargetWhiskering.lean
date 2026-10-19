/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# Target horizontal isomorphisms in actual two-square routes

Changing either target horizontal functor moves its specified isomorphism to the target of
exactly the same pasted route. The second change uses the actual isomorphism naturality.
The intended upstream owner is `Aglib.CategoryTheory.Functor.IsoSquareRouteTargetWhiskering`.
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
  {a a' : A₀ ⥤ A₁} {b b' : A₁ ⥤ A₂} {N N' : B₀ ⥤ B₁} {M M' : B₁ ⥤ B₂}
  {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁} {E₂ : A₂ ⥤ B₂}

/-- Changing the first target horizontal functor retains the full pasted route. -/
theorem isoSquareRoute_leftTargetIso (r : N ≅ N')
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) :
    isoSquareRoute (s ≪≫ isoWhiskerLeft E₀ r) t =
      isoSquareRoute s t ≪≫ isoWhiskerLeft E₀ (isoWhiskerRight r M) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]

/-- Changing the second target horizontal functor uses its whole naturality square. -/
theorem isoSquareRoute_rightTargetIso (r : M ≅ M')
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) :
    isoSquareRoute s (t ≪≫ isoWhiskerLeft E₁ r) =
      isoSquareRoute s t ≪≫ isoWhiskerLeft E₀ (isoWhiskerLeft N r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  simpa only [Functor.comp_obj, Category.assoc] using
    congrArg (fun k => t.hom.app (a.obj X) ≫ k) (r.hom.naturality (s.hom.app X)).symm

end CategoryTheory.Functor
