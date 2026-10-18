/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Bass.LoopStrengthConeAction

/-! The actual second-stage strength preserves the twice induced original action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
open ConeTrack LoopStrength LoopConeTrack
open LoopStrengthConeAction
open scoped unitInterval
universe u v w
variable {C : Type u} [Category.{v} C]
    (Q : C ⥤ Arrow (Arrow C)) (L : C ⥤ C) (c : 𝟭 C ⟶ L)
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    (F : C ⥤ Quillen.LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (c.app X)) (F.map (c.app X)))
    (hH : ∀ {X Y} (g : X ⟶ Y) n r x,
      (F.map (L.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

example (X : C) (r : unitInterval) :
    strength Q (diagram Q F) X ≫ parameterLoopingMap (parameterLoopingMap
      ((action Q L c χ hχ (diagram Q F) (action Q L c χ hχ F H hH)
        (action_naturality Q L c χ hχ F H hH) X).at r)) =
    parameterLoopingMap
      ((action Q L c χ hχ (diagram Q F ⋙ parameterLoopingFunctor)
        (fun Y => (action Q L c χ hχ F H hH Y).parameterLooping)
        (loop_naturality L c (diagram Q F) (action Q L c χ hχ F H hH)
          (action_naturality Q L c χ hχ F H hH)) X).at r) ≫
      strength Q (diagram Q F) (L.obj X) :=
  strength_action Q L c χ hχ (diagram Q F) (action Q L c χ hχ F H hH)
    (action_naturality Q L c χ hχ F H hH) X r
