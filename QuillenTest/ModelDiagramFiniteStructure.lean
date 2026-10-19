/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramConeFiniteStructure

/-! Regression for arbitrary Bass stages and the exact row-refinement eventual cutoff. -/
public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
universe u v w

/-- Stage one is instantiated without any later-stage Omega hypothesis. -/
theorem firstStageRange {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ Model.{w}) (X : C) (n j : ℕ) (hj : 0 < j) (hr : j < 2 * n + 2) :
    Function.Bijective (homotopyGroupMap (N := Fin j)
      ((((strictDiagramIterate Q 1).obj (F ⋙ prespectrumFunctor)).obj X).structureMap
        (n + 1 + 2))
      ((((strictDiagramIterate Q 1).obj (F ⋙ prespectrumFunctor)).obj X).map_point
        (n + 1 + 2))) := by
  have h := modelDiagramIterate_structure_bijective Q 1 F X n j hj hr
  exact h

example {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (i : ℕ) (F : C ⥤ Model.{w}) (X : C) (n k : ℕ)
    (hn : i + 2 ≤ n) (hk : k + 2 < 2 * n - (2 * i + 2)) :
    Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).structureMap (n + 1))
      ((mappingCone (StrictSquare.comparison
        (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).mapArrow.mapArrow.obj
          (Q.obj X)))).map_point _)) := by
  have h := modelDiagramIterate_cone_structure_bijective Q i F X (n - (i + 2)) k (by omega)
  rw [show n - (i + 2) + i + 3 = n + 1 by omega] at h
  exact h
