/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.DiagramTransportGroupNaturality

/-! # Original Laurent representatives under group-functor transport

The client evaluates the commuting quotient square on an arbitrary original
Laurent representative, retaining the actual group transformation and chart
identification rather than just an abstract isomorphism of quotient objects.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Quillen.Bass.TwoChart
universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace DiagramTransportGroupNaturalityConsumers

/-- Transport and a group transformation retain the same original Laurent representative. -/
theorem original_laurent_representative
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P L : C ⥤ C} {P' L' : D ⥤ D} (p m : P ⟶ L) (p' m' : P' ⟶ L')
    (T : D ⥤ C) (eP : P' ⋙ T ≅ T ⋙ P) (eL : L' ⋙ T ≅ T ⋙ L)
    (hp : ∀ X, T.map (p'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ p.app (T.obj X))
    (hm : ∀ X, T.map (m'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ m.app (T.obj X))
    {F G : C ⥤ AddCommGrpCat.{w}} (α : F ⟶ G) (X : D)
    (x : F.obj (T.obj (L'.obj X))) :
    (contractionTransportIso p m p' m' T eP eL hp hm G).hom.app X
        ((contractionMap p' m' (Functor.whiskerLeft T α)).app X
          ((contractionπ p' m' (T ⋙ F)).app X x)) =
      (contractionπ p m G).app (T.obj X)
        (α.app (L.obj (T.obj X)) (F.map (eL.hom.app X) x)) := by
  have h := congrArg (fun f ↦ (contractionπ p' m' (T ⋙ F)).app X ≫ f)
    (contractionTransportIso_groupMap p m p' m' T eP eL hp hm α X)
  rw [contractionTransportIso_π_assoc, contractionMap_π] at h
  exact congrArg (fun f ↦ f x) h

end DiagramTransportGroupNaturalityConsumers
