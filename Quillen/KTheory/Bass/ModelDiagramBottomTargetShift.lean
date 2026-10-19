/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramBottomComparison
public import Quillen.KTheory.Bass.StrictDiagramIndexTargetShift

/-!
# The first two genuine Model bottom shifts

The original Laurent representative commutes with the exact integer-degree
transport in the bottom successor. Both the genuine signed shift and the
equality-induced finite-stage transport remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent
universe u w
namespace Quillen.KTheory.Bass
variable {R : CommRingCat.{u}} (F : Under R ⥤ Model.{w})

private theorem coneDiagram_obj (i : ℕ) (a : Under R) :
    (modelDiagramTwoChartConeDiagram F i).obj a =
      mappingCone (StrictSquare.comparison (modelDiagramTwoChartSquare F i a)) := rfl

private theorem degree_transport {E F : LoopPrespectrum.{w}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    (stableHomotopyFunctor d).map f ≫
        eqToHom (congrArg (fun k => stableHomotopyGroup F k) h) =
      eqToHom (congrArg (fun k => stableHomotopyGroup E k) h) ≫
        (stableHomotopyFunctor e).map f := by
  subst e
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Every original bottom representative retains its exact integer transport and shift. -/
theorem modelDiagramBottomSuccessor_targetShift (i : ℕ) (a : Under R) :
    (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) ≫
        (modelDiagramBottomSuccessorIso F i).inv.app a =
      eqToHom (congrArg
        (fun d : ℤ => stableHomotopyGroup (modelDiagramTwoChartSquare F i a).right.right d)
        (show -(i : ℤ) = -((i + 1 : ℕ) : ℤ) + 1 by omega)) ≫
      StrictDiagramIndexRow.targetShift (modelDiagramTwoChartSquare F i a)
        (-((i + 1 : ℕ) : ℤ)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((modelDiagramTwoChartSuccessorIso F i).inv.app a) := by
  rw [modelDiagramBottomSuccessorIso_inv_app]
  dsimp only [StrictDiagramIndexRow.targetShift]
  rw [← Category.assoc, ← Category.assoc, degree_transport _
    (show -(i : ℤ) = -((i + 1 : ℕ) : ℤ) + 1 by omega)]
  simp only [Category.assoc, coneDiagram_obj]

/-- The first equality-induced whole row map is literally the identity. -/
theorem modelDiagramTwoChartSuccessorIso_zero_inv :
    (modelDiagramTwoChartSuccessorIso F 0).inv = 𝟙 (modelDiagramTwoChartDiagram F 1) := rfl

/-- The second equality-induced whole row map is literally the identity. -/
theorem modelDiagramTwoChartSuccessorIso_one_inv :
    (modelDiagramTwoChartSuccessorIso F 1).inv = 𝟙 (modelDiagramTwoChartDiagram F 2) := rfl

end Quillen.KTheory.Bass
