/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexTargetShift

/-!
# Two original Laurent representatives under an actual index comparison

The two target inclusions and inverse signed shifts are transported by the
original second finite index-plus-row isomorphism. The double target corner
keeps both index arrows and the row isomorphism in their original order.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u₁ v₁ u₂ v₂ w
namespace Quillen.KTheory.Bass.StrictDiagramIndexRow
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Both unchanged Laurent target inclusions, with their original inverse signed shifts. -/
def doubleTargetShift (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
    (X : C) (d : ℤ) :
    (stableHomotopyFunctor ((d + 1) + 1)).obj
        (F.obj (Q.obj (Q.obj X).right.right).right.right) ⟶
      (stableHomotopyFunctor d).obj (((strictDiagramIterate Q 2).obj F).obj X) :=
  targetShift (F.mapArrow.mapArrow.obj (Q.obj (Q.obj X).right.right)) (d + 1) ≫
    targetShift (((strictDiagramFunctor Q).obj F).mapArrow.mapArrow.obj (Q.obj X)) d

variable (K : C ⥤ D) (Q₁ : C ⥤ Arrow (Arrow C)) (Q₂ : D ⥤ Arrow (Arrow D))
    (α : K ⋙ Q₂ ≅ Q₁ ⋙ K.mapArrow.mapArrow)
    {F : D ⥤ LoopPrespectrum.{w}} {G : C ⥤ LoopPrespectrum.{w}} (ρ : K ⋙ F ≅ G)

/-- The actual double Laurent corner retains both index arrows before the original row map. -/
def doubleTargetCorner (X : C) :
    F.obj (Q₂.obj (Q₂.obj (K.obj X)).right.right).right.right ⟶
      G.obj (Q₁.obj (Q₁.obj X).right.right).right.right :=
  F.map (Q₂.map (α.hom.app X).right.right).right.right ≫
    F.map (α.hom.app (Q₁.obj X).right.right).right.right ≫
    ρ.hom.app (Q₁.obj (Q₁.obj X).right.right).right.right

private theorem mapSquare_right_right (F : D ⥤ LoopPrespectrum.{w})
    (S : Arrow (Arrow D)) :
    (F.mapArrow.mapArrow.obj S).right.right = F.obj S.right.right := rfl

private theorem two_steps {E : Type*} [Category E]
    {A B C D E₁ F₁ G H : E}
    (a : A ⟶ B) (b : B ⟶ C) (f : C ⟶ D)
    (u : B ⟶ E₁) (v : E₁ ⟶ F₁) (w : F₁ ⟶ D)
    (k : A ⟶ G) (l : G ⟶ E₁) (m : G ⟶ H) (n : H ⟶ F₁)
    (hb : b ≫ f = u ≫ v ≫ w) (ha : a ≫ u = k ≫ l)
    (hl : l ≫ v = m ≫ n) : a ≫ b ≫ f = k ≫ m ≫ n ≫ w := by
  rw [hb, ← Category.assoc a, ha]
  simp only [Category.assoc]
  rw [← Category.assoc l, hl]
  simp only [Category.assoc]

/-- The original second finite comparison transports both genuine signed representatives. -/
@[reassoc]
theorem finiteIso_doubleTargetShift (X : C) (d : ℤ) :
    doubleTargetShift Q₂ F (K.obj X) d ≫
        (stableHomotopyFunctor d).map ((finiteIso K Q₁ Q₂ α ρ 2).hom.app X) =
      (stableHomotopyFunctor ((d + 1) + 1)).map (doubleTargetCorner K Q₁ Q₂ α ρ X) ≫
        doubleTargetShift Q₁ G X d := by
  have hb := finiteIso_one_targetShift K Q₁ Q₂ α (finiteIso K Q₁ Q₂ α ρ 1) X d
  have hb' := hb
  simp only [Functor.map_comp, Category.assoc] at hb'
  have ha := (diagram_targetShift_naturality Q₂ (F := F)
    (α.hom.app X).right.right (d + 1)).symm
  have hl := finiteIso_one_targetShift K Q₁ Q₂ α ρ (Q₁.obj X).right.right (d + 1)
  have h := two_steps _ _ _ _ _ _ _ _ _ _ hb' ha hl
  simpa only [doubleTargetShift, finiteIso_two_hom, doubleTargetCorner,
    Functor.map_comp, Category.assoc, Functor.comp_obj, strictDiagramIterate,
    Functor.id_obj, mapSquare_right_right] using h

end Quillen.KTheory.Bass.StrictDiagramIndexRow
