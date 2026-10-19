/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.StrictDiagramIndexDoubleShift
public import Quillen.KTheory.Bass.GeometricConeDoubleBottomShift

/-!
# The actual Scheme double target shift and normalization

The generic two-target representative is the same original Scheme representative.
The established second normalization therefore retains its genuine transpose sign.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.GeometricConeInterchange

private theorem loop_square {C : Type*} [Category C]
    (F : C ⥤ LoopPrespectrum.{w}) (S : Arrow (Arrow C)) :
    (F ⋙ parameterLoopingFunctor).mapArrow.mapArrow.obj S =
      LoopFactor.loopSquare (F.mapArrow.mapArrow.obj S) := rfl

private theorem squareFunctor_obj (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.obj X = square X := rfl

private theorem square_right_right (X : Scheme.{u}ᵒᵖ) :
    (square X).right.right = laurent.op.obj X := rfl

/-- The two target shifts are exactly the original geometric double-bottom representative. -/
theorem doubleTargetShift_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    StrictDiagramIndexRow.doubleTargetShift squareFunctor F X d =
      doubleBottomRepresentative F X d := by
  simp only [StrictDiagramIndexRow.doubleTargetShift, StrictDiagramIndexRow.targetShift,
    doubleBottomRepresentative, NormalizedStageMap.bass_eq_loop_cone,
    SchemeIteratedSeedTransition.coneFunctor_obj_eq, loop_square,
    SchemeIteratedSeedTransition.coneDiagram_obj_eq, squareFunctor_obj, square_right_right,
    Category.assoc]

/-- The actual second normalization retains the transpose sign on these same representatives. -/
theorem doubleTargetShift_stageMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    StrictDiagramIndexRow.doubleTargetShift squareFunctor F X d ≫
        (stableHomotopyFunctor d).map ((NormalizedStageMap.stageMap squareFunctor 2 F).app X) ≫
        (doubleNormalizedShift F X d).hom =
      -((stableHomotopyFunctor ((d + 1) + 1)).map (doubleLaurentInclusion F X)) := by
  rw [doubleTargetShift_eq]
  exact doubleBottomRepresentative_stageMap F X d

end Quillen.KTheory.Bass.GeometricConeInterchange
