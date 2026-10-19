/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowTargetInputNaturality

/-! Original input transformations preserve both zero-level rows and the whole target square. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass ModelDiagramRowRefinement
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.ModelDiagramRowInputNaturality
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) {F G : C ⥤ Model.{w}} (η : F ⟶ G) (X : C)

/-- Both zero-level row coordinates survive the actual exact input transformation. -/
theorem input_zero (γ : Path (Path.refl ((source Q i F X).point 2))
    (Path.refl ((source Q i F X).point 2))) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((inputMap Q i η X).map 0 γ) r) s =
      ((inputSourceMap Q i η).app X).map 2 (γ r s) := rfl

/-- Positive rows retain their independent coordinate under the same input transformation. -/
theorem input_succ (k : ℕ)
    (γ : Path ((source Q i F X).point (k + 2)) ((source Q i F X).point (k + 2)))
    (r : unitInterval) :
    Path.toContinuousMap ((inputMap Q i η X).map (k + 1) γ) r =
      ((inputSourceMap Q i η).app X).map (k + 2) (γ r) := rfl

/-- The entire actual counit/refinement square is preserved under an arbitrary exact input map. -/
theorem target_square :
    parameterLoopingMap (suspensionConeMap (parameterLoopingMap
      ((inputSourceMap Q i η).app X))) ≫
        ModelDiagramRowStabilizedTarget.refinement Q i G X =
    ModelDiagramRowStabilizedTarget.refinement Q i F X ≫
      (ModelDiagramRowStabilizedTarget.inputNatTrans Q i η).app X :=
  ModelDiagramRowStabilizedTarget.refinement_input_naturality Q i η X

end QuillenTest.ModelDiagramRowInputNaturality
