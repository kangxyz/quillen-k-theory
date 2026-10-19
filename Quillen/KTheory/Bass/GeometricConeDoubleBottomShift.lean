/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricConeDoubleLaurent
public import Quillen.KTheory.Bass.NormalizedStageLowStages
public import Quillen.KTheory.Bass.LoopStrengthSignedShift
public import Quillen.KTheory.Bass.SchemeConeValueIdentification

/-!
# Original double-Laurent representatives through the second normalization

The two original target inclusions, separated by the original inverse signed
shifts, give the second iterated-bottom representative. The actual second
normalization and both forward shifts send it to minus the unlooped
double-Laurent inclusion. The geometric factor swap is not simplified.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.StrictSquare

universe u w

namespace Quillen.KTheory.Bass.GeometricConeInterchange

private theorem squareFunctor_obj (X : Scheme.{u}ᵒᵖ) :
    squareFunctor.obj X = square X := rfl

private theorem square_target (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) :
    (F.mapArrow.mapArrow.obj (square X)).right.right = F.obj (laurent.op.obj X) := rfl

/-- The actual second bottom representative uses both original inverse signed shifts. -/
def doubleBottomRepresentative (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor ((d + 1) + 1)).obj (F.obj (laurent.op.obj (laurent.op.obj X))) ⟶
      (stableHomotopyFunctor d).obj (((strictDiagramIterate squareFunctor 2).obj F).obj X) :=
  (stableHomotopyFunctor ((d + 1) + 1)).map
      (mappingConeInclusion (comparison (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))))) ≫
    (parameterStableHomotopyIso ((coneFunctor.obj F).obj (laurent.op.obj X)) (d + 1)).inv ≫
    (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion (comparison
      (LoopFactor.loopSquare ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X))))) ≫
    (parameterStableHomotopyIso (mappingCone (comparison
      (LoopFactor.loopSquare ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X))))) d).inv

/-- Both original forward shifts from the actual second normalized object. -/
def doubleNormalizedShift (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).obj ((NormalizedStageMap.normalized squareFunctor 2 F).obj X) ≅
      (stableHomotopyFunctor ((d + 1) + 1)).obj ((coneFunctor.obj (coneFunctor.obj F)).obj X) :=
  parameterStableHomotopyIso
      (parameterLooping ((coneFunctor.obj (coneFunctor.obj F)).obj X)) d ≪≫
    parameterStableHomotopyIso ((coneFunctor.obj (coneFunctor.obj F)).obj X) (d + 1)

/-- The original representative acquires the actual transpose sign under normalization. -/
theorem doubleBottomRepresentative_stageMap (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    doubleBottomRepresentative F X d ≫
        (stableHomotopyFunctor d).map ((NormalizedStageMap.stageMap squareFunctor 2 F).app X) ≫
        (doubleNormalizedShift F X d).hom =
      -((stableHomotopyFunctor ((d + 1) + 1)).map (doubleLaurentInclusion F X)) := by
  rw [NormalizedStageMap.stageMap_two_app]
  have h := LoopFactor.strength_inclusion_signedShift squareFunctor (coneFunctor.obj F) X d
  have hc := congrArg (fun k => (stableHomotopyFunctor ((d + 1) + 1)).map
    (mappingConeInclusion (comparison (F.mapArrow.mapArrow.obj (square (laurent.op.obj X))))) ≫ k) h
  simpa only [doubleBottomRepresentative, doubleNormalizedShift, doubleLaurentInclusion,
    Iso.trans_hom, CategoryTheory.Functor.map_comp, Category.assoc, Preadditive.comp_neg,
    SchemeIteratedSeedTransition.coneFunctor_obj_obj_eq,
    SchemeIteratedSeedTransition.coneFunctor_obj_eq,
    SchemeIteratedSeedTransition.coneDiagram_obj_eq, squareFunctor_obj, square_target] using hc

end Quillen.KTheory.Bass.GeometricConeInterchange
