/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SmallModel.Whiskering
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-! # Common-universe transport of a whole isomorphism cube

The actual up/down functors lift all edges and independently supplied faces of a cube.
Its two complete routes agree whenever the original routes agree. No face or compatibility
is replaced by a chosen equality after lifting.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v
namespace Quillen.Waldhausen

/-- The actual common-universe lift of an entire natural isomorphism. -/
def smallModelCubeIso {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (e : F ≅ G) : smallModelFunctor F ≅ smallModelFunctor G :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down.{v, u, 0} e) AsSmall.up.{v, u, 0}

private theorem cubeIso_hom_app_down {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (e : F ≅ G) (X : SmallModel C) :
    ((smallModelCubeIso e).hom.app X).down = e.hom.app (AsSmall.down.obj X) := rfl

private theorem smallFunctor_map_down {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {X Y : SmallModel C} (f : X ⟶ Y) :
    ((smallModelFunctor F).map f).down = F.map f.down := rfl

private theorem route_hom_app {C₀ C₁ C₂ D₀ D₁ D₂ : Type u}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂]
    {a : C₀ ⥤ C₁} {b : C₁ ⥤ C₂} {N : D₀ ⥤ D₁} {M : D₁ ⥤ D₂}
    {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    (s : a ⋙ E₁ ≅ E₀ ⋙ N) (t : b ⋙ E₂ ≅ E₁ ⋙ M) (X : C₀) :
    (isoSquareRoute s t).hom.app X = t.hom.app (a.obj X) ≫ M.map (s.hom.app X) := by
  simp only [isoSquareRoute, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]

variable {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type u}
  [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
  [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
  {P : C₀ ⥤ C₁} {A : C₁ ⥤ C₂} {B : C₀ ⥤ C₃} {Q : C₃ ⥤ C₂}
  {p : D₀ ⥤ D₁} {a : D₁ ⥤ D₂} {b : D₀ ⥤ D₃} {q : D₃ ⥤ D₂}
  {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}

/-- The original whole cube survives the actual common-universe transport on every edge. -/
theorem smallModelIsoCube (R : P ⋙ A ≅ B ⋙ Q) (r : p ⋙ a ≅ b ⋙ q)
    (sP : P ⋙ E₁ ≅ E₀ ⋙ p) (sA : A ⋙ E₂ ≅ E₁ ⋙ a)
    (sB : B ⋙ E₃ ≅ E₀ ⋙ b) (sQ : Q ⋙ E₂ ≅ E₃ ⋙ q)
    (h : isoWhiskerRight R E₂ ≪≫ isoSquareRoute sB sQ =
      isoSquareRoute sP sA ≪≫ isoWhiskerLeft E₀ r) :
    isoWhiskerRight (smallModelCubeIso R) (smallModelFunctor E₂) ≪≫
        isoSquareRoute (a := smallModelFunctor B) (b := smallModelFunctor Q)
          (N := smallModelFunctor b) (M := smallModelFunctor q)
          (E₀ := smallModelFunctor E₀) (E₁ := smallModelFunctor E₃)
          (E₂ := smallModelFunctor E₂) (smallModelCubeIso sB) (smallModelCubeIso sQ) =
      isoSquareRoute (a := smallModelFunctor P) (b := smallModelFunctor A)
          (N := smallModelFunctor p) (M := smallModelFunctor a)
          (E₀ := smallModelFunctor E₀) (E₁ := smallModelFunctor E₁)
          (E₂ := smallModelFunctor E₂) (smallModelCubeIso sP) (smallModelCubeIso sA) ≪≫
        isoWhiskerLeft (smallModelFunctor E₀) (smallModelCubeIso r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  have he := NatTrans.congr_app (congrArg Iso.hom h) (AsSmall.down.obj X)
  simp only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, route_hom_app] at he
  change E₂.map (R.hom.app (AsSmall.down.obj X)) ≫
      (𝟙 _ ≫ sQ.hom.app (B.obj (AsSmall.down.obj X)) ≫ 𝟙 _ ≫
        q.map (sB.hom.app (AsSmall.down.obj X)) ≫ 𝟙 _) =
    (𝟙 _ ≫ sA.hom.app (P.obj (AsSmall.down.obj X)) ≫ 𝟙 _ ≫
      a.map (sP.hom.app (AsSmall.down.obj X)) ≫ 𝟙 _) ≫
        r.hom.app (E₀.obj (AsSmall.down.obj X))
  simpa only [Category.id_comp, Category.comp_id] using he

end Quillen.Waldhausen
