/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
public import Quillen.KTheory.Bass.ModelDiagramRowInputNaturality

/-!
# Proper row replacement under exact Model transformations

The whole proper target replacement is natural for the original exact Model
maps, including supported-to-ambient and restriction maps. This statement
retains the computed row comparison and actual suspension evaluation counit.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) {F G : C ⥤ Model.{w}} (η : F ⟶ G)

/-- The actual input map on whole proper target diagrams. -/
def inputNatTrans : targetDiagram Q i F ⟶ targetDiagram Q i G :=
  Functor.whiskerRight (ModelDiagramRowRefinement.inputNatTrans Q i η)
    parameterLoopingFunctor

/-- The original replacement counits and computed row maps preserve the input transformation. -/
theorem refinement_input_naturality (X : C) :
    parameterLoopingMap (suspensionConeMap (parameterLoopingMap
      ((ModelDiagramRowRefinement.inputSourceMap Q i η).app X))) ≫ refinement Q i G X =
    refinement Q i F X ≫ (inputNatTrans Q i η).app X := by
  let g : cone Q i F X ⟶ cone Q i G X :=
    (ModelDiagramRowRefinement.inputSourceMap Q i η).app X
  have hρ : g ≫ ModelDiagramRowRefinement.comparison Q i G X =
      ModelDiagramRowRefinement.comparison Q i F X ≫
        ModelDiagramRowRefinement.inputMap Q i η X :=
    ModelDiagramRowRefinement.comparison_input_naturality Q i η X
  change parameterLoopingFunctor.map (suspensionConeMap (parameterLoopingMap g)) ≫
      parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i G X) ≫
        ModelDiagramRowRefinement.comparison Q i G X) =
    parameterLoopingFunctor.map (suspensionLoopCounit (cone Q i F X) ≫
      ModelDiagramRowRefinement.comparison Q i F X) ≫
        parameterLoopingFunctor.map (ModelDiagramRowRefinement.inputMap Q i η X)
  rw [← parameterLoopingFunctor.map_comp, ← parameterLoopingFunctor.map_comp]
  apply congrArg parameterLoopingFunctor.map
  rw [← Category.assoc, suspensionLoopCounit_naturality, Category.assoc, hρ,
    Category.assoc]

end Quillen.KTheory.Bass.ModelDiagramRowStabilizedTarget
