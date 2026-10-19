/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareRouteNormalization

/-!
# Whole cube coherence under independent edge normalization

All twelve edges may be replaced by specified isomorphic functors. Transporting each original
face by its two actual path normalizations preserves the entire original cube equation.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w₀ z₀ w₁ z₁ w₂ z₂ w₃ z₃
namespace CategoryTheory.Functor

private theorem normalized_right
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    {F F' G G' : C ⥤ D} {H H' : D ⥤ E}
    (s : F ≅ G) (nF : F ≅ F') (nG : G ≅ G') (e : H ≅ H') :
    isoWhiskerRight (nF.symm ≪≫ s ≪≫ nG) H' =
      (pathNormalization nF e).symm ≪≫ isoWhiskerRight s H ≪≫ pathNormalization nG e := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [pathNormalization, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerRight_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [← H.map_comp_assoc, ← H.map_comp_assoc, e.hom.naturality]
  rw [Iso.inv_hom_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]

private theorem normalized_left
    {C : Type u₀} [Category.{v₀} C] {D : Type u₁} [Category.{v₁} D]
    {E : Type u₂} [Category.{v₂} E]
    {F F' G G' : D ⥤ E} {H H' : C ⥤ D}
    (s : F ≅ G) (nF : F ≅ F') (nG : G ≅ G') (e : H ≅ H') :
    isoWhiskerLeft H' (nF.symm ≪≫ s ≪≫ nG) =
      (pathNormalization e nF).symm ≪≫ isoWhiskerLeft H s ≪≫ pathNormalization e nG := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [pathNormalization, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerRight_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc]
  rw [s.hom.naturality_assoc, ← G.map_comp_assoc, Iso.inv_hom_id_app,
    G.map_id, Category.id_comp]

variable {C₀ : Type u₀} [Category.{v₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {D₀ : Type w₀} [Category.{z₀} D₀]
  {D₁ : Type w₁} [Category.{z₁} D₁] {D₂ : Type w₂} [Category.{z₂} D₂]
  {D₃ : Type w₃} [Category.{z₃} D₃]
  {P P' : C₀ ⥤ C₁} {A A' : C₁ ⥤ C₂}
  {B B' : C₀ ⥤ C₃} {Q Q' : C₃ ⥤ C₂}
  {p p' : D₀ ⥤ D₁} {a a' : D₁ ⥤ D₂}
  {b b' : D₀ ⥤ D₃} {q q' : D₃ ⥤ D₂}
  {E₀ E₀' : C₀ ⥤ D₀} {E₁ E₁' : C₁ ⥤ D₁}
  {E₂ E₂' : C₂ ⥤ D₂} {E₃ E₃' : C₃ ⥤ D₃}

/-- Independent edge conjugations preserve the original six-face cube equation. -/
theorem isoCube_faceNormalization
    (R : P ⋙ A ≅ B ⋙ Q) (r : p ⋙ a ≅ b ⋙ q)
    (sP : P ⋙ E₁ ≅ E₀ ⋙ p) (sA : A ⋙ E₂ ≅ E₁ ⋙ a)
    (sB : B ⋙ E₃ ≅ E₀ ⋙ b) (sQ : Q ⋙ E₂ ≅ E₃ ⋙ q)
    (h : isoWhiskerRight R E₂ ≪≫ isoSquareRoute sB sQ =
      isoSquareRoute sP sA ≪≫ isoWhiskerLeft E₀ r)
    (nP : P ≅ P') (nA : A ≅ A') (nB : B ≅ B') (nQ : Q ≅ Q')
    (np : p ≅ p') (na : a ≅ a') (nb : b ≅ b') (nq : q ≅ q')
    (e₀ : E₀ ≅ E₀') (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') (e₃ : E₃ ≅ E₃') :
    isoWhiskerRight (faceNormalization R nP nA nB nQ) E₂' ≪≫
        isoSquareRoute (faceNormalization sB nB e₃ e₀ nb)
          (faceNormalization sQ nQ e₂ e₃ nq) =
      isoSquareRoute (faceNormalization sP nP e₁ e₀ np)
          (faceNormalization sA nA e₂ e₁ na) ≪≫
        isoWhiskerLeft E₀' (faceNormalization r np na nb nq) := by
  rw [isoSquareRoute_faceNormalization, isoSquareRoute_faceNormalization]
  simp only [faceNormalization]
  rw [normalized_right R (pathNormalization nP nA) (pathNormalization nB nQ) e₂,
    normalized_left r (pathNormalization np na) (pathNormalization nb nq) e₀]
  have h' := congrArg (fun z =>
    (pathNormalization (pathNormalization nP nA) e₂).symm ≪≫ z ≪≫
      pathNormalization e₀ (pathNormalization nb nq)) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc] using h'

end CategoryTheory.Functor
