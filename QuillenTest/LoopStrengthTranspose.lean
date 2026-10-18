/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.LoopStrengthTranspose

/-! Regression for all three original loop times in the finite strength interchange. -/
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
open LoopStrengthTranspose IteratedLoopStrength
open scoped Topology unitInterval
universe u v w
variable {C : Type u} [Category.{v} C]

example (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ Quillen.LoopPrespectrum.{w}) (X : C)
    (n : ℕ) (r s t : unitInterval)
    (z : (((strictDiagramFunctor Q).obj
      ((F ⋙ parameterLoopingFunctor) ⋙ parameterLoopingFunctor)).obj X).space n) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      (((iteratedStrength Q 2 F).app X).map n
        ((((strictDiagramFunctor Q).map (transposeDiagram F)).app X).map n z)) r) s) t =
      Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
        (((iteratedStrength Q 2 F).app X).map n z) s) r) t := by
  have h := congrArg (fun a => (a.app X).map n z)
    (iteratedStrength_two_transpose Q F)
  exact congrArg (fun γ => Path.toContinuousMap
    (Path.toContinuousMap (Path.toContinuousMap γ r) s) t) h

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (X : C) (n : ℕ)
    (r s : unitInterval)
    (γ : (parameterLooping (parameterLooping (F.obj X))).space n) :
    ((evaluationTwo F r s).app X).map n γ =
      Path.toContinuousMap (Path.toContinuousMap γ r) s := rfl

#print axioms iteratedStrength_two_evaluation
#print axioms iteratedStrength_two_transpose
