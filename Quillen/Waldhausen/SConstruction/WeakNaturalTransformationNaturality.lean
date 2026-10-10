/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.SConstruction.WeakNaturalTransformation
public import Quillen.Waldhausen.SConstruction.NerveCylinderNaturality

/-! # Strict naturality of the original weak-transformation cylinder

The categorical nerve cylinder commutes with actual postcomposition.
Consequently the original S-cylinder maps commute with exact functor
precomposition and postcomposition, retaining their original endpoints.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen

private theorem mk₁_whiskerRight {J : Type u} [Category.{v} J]
    {C : Type u'} [Category.{v'} C] {D : Type u''} [Category.{v''} D]
    {A B : J ⥤ C} (η : A ⟶ B) (F : C ⥤ D) :
    ComposableArrows.mk₁ (whiskerRight η F) =
      ComposableArrows.mk₁ η ⋙ (whiskeringRight J C D).obj F := by
  apply ComposableArrows.ext₁ (F := ComposableArrows.mk₁ (whiskerRight η F))
    (G := ComposableArrows.mk₁ η ⋙ (whiskeringRight J C D).obj F) rfl rfl
  simp

/-- The whole original categorical cylinder commutes with every actual functor. -/
theorem nerveCylinderDiagram_postcomp {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {n m : SimplexCategory}
    {A B : Grid₂ n m ⥤ C} (η : A ⟶ B) (F : C ⥤ D) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram η τ ⋙ F = nerveCylinderDiagram (whiskerRight η F) τ := by
  unfold nerveCylinderDiagram
  rw [mk₁_whiskerRight]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact F.map_comp _ _

section Exact
variable {B C D E : Type u} [Category.{v} B] [Category.{v} C]
  [Category.{v} D] [Category.{v} E]
  (T : Structure B) (V : Structure C) (W : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

/-- Exact postcomposition retains the entire original simplicial cylinder. -/
theorem weakNaturalTransformationCylinder_postcompose {H : D ⥤ E}
    (hH : IsExact W.cof W.weq U.cof U.weq H) :
    weakNaturalTransformationCylinder V W hF hG η hη ≫ sSetMap hH =
      weakNaturalTransformationCylinder V U (hF.comp hH) (hG.comp hH)
        (whiskerRight η H) (fun X ↦ hH.weak _ (hη X)) := by
  ext n z : 4
  apply Subtype.ext
  exact nerveCylinderDiagram_postcomp (whiskerLeft z.1.val η) H z.2.down

/-- Exact precomposition retains the entire original simplicial cylinder. -/
theorem weakNaturalTransformationCylinder_precompose {H : B ⥤ C}
    (hH : IsExact T.cof T.weq V.cof V.weq H) :
    sSetMap hH ▷ Δ[1] ≫ weakNaturalTransformationCylinder V W hF hG η hη =
      weakNaturalTransformationCylinder T W (hH.comp hF) (hH.comp hG)
        (whiskerLeft H η) (fun X ↦ hη (H.obj X)) := by
  ext n z : 4
  rfl

end Exact
end Quillen.Waldhausen
