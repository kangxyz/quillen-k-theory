/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget

/-! Regression laws for the actual proper row target and its original successor unit. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
open ModelDiagramRowStabilizedTarget
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w}) {X Y : C} (f : X ⟶ Y)

/-- The actual zero target arrow retains all three independent path coordinates. -/
theorem map_zero (γ : (target Q i F X).space 0) (a r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      (((targetDiagram Q i F).map f).map 0 γ) a) r) s =
      ((ModelDiagramRowRefinement.sourceDiagram Q i F).map f).map 2 (Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap γ a) r) s) := rfl

/-- Positive target levels retain both the external loop and genuine row coordinate. -/
theorem map_succ (k : ℕ) (γ : (target Q i F X).space (k + 1))
    (a r : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (((targetDiagram Q i F).map f).map (k + 1) γ) a) r =
      ((ModelDiagramRowRefinement.sourceDiagram Q i F).map f).map (k + 2) (Path.toContinuousMap (Path.toContinuousMap γ a) r) := rfl

/-- The unit triangle is tested on the original successor, including its actual transport. -/
theorem current_triangle :
    suspensionLoopUnit
        (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X) ≫
      currentRefinement Q i F X =
    eqToHom (ModelDiagramSuspension.successor_obj Q i F X) ≫
      parameterLoopingMap (ModelDiagramRowRefinement.comparison Q i F X) :=
  current_unit_refinement Q i F X

end QuillenTest.ModelDiagramRowStabilizedTarget
