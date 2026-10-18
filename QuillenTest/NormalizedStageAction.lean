/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.KTheory.Bass.NormalizedStageAction

/-! All original track times survive the unchanged finite stage map. -/
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.KTheory.Bass
open NaturalTrack NormalizedStageMap
open scoped unitInterval
universe u v w
variable {C : Type u} [Category.{v} C] {L : C ⥤ C} {c : 𝟭 C ⟶ L}
    (Q : C ⥤ Arrow (Arrow C))
    (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
    (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
      ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
        ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))
    {F : C ⥤ Quillen.LoopPrespectrum.{w}} (A : Track L c F)

example (i : ℕ) (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramIterate Q i).obj F).obj X).space n) :
    ((A.normalized Q χ hχ i).homotopy X).level n
        (r, ((stageMap Q i F).app X).map n x) =
      ((stageMap Q i F).app (L.obj X)).map n
        (((A.stages Q χ hχ i).homotopy X).level n (r, x)) :=
  congrArg (fun k => k.map n x) (stageMap_equivariant Q χ hχ A i X r)
