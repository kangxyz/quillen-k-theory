/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.SchemeConeValueIdentification
public import Quillen.KTheory.Bass.GeometricSeedCospan
public import Quillen.KTheory.Bass.LoopFactor

/-! # The complete object aliases in the original finite seed cospan -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeIteratedSeedTransition

/-- The geometric-square cone diagram is the unchanged original cone diagram. -/
theorem geometricSquare_coneDiagram_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    mappingConeDiagram (SquareConeStrength.comparison
      (GeometricSquareInterchange.geometricSquare F)) = ConeTrack.diagram squareFunctor F := rfl

/-- The original Bass value is precisely the parameter loop on the original square cone. -/
theorem bass_obj_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    ((strictDiagramFunctor squareFunctor).obj F).obj X =
      parameterLooping (mappingCone (StrictSquare.comparison
        (F.mapArrow.mapArrow.obj (square X)))) := rfl

/-- The original Bass square is the original loop square on its original cone. -/
theorem bass_square_eq (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    ((strictDiagramFunctor squareFunctor).obj F).mapArrow.mapArrow.obj (square X) =
      LoopFactor.loopSquare
        ((ConeTrack.diagram squareFunctor F).mapArrow.mapArrow.obj (square X)) := rfl

end Quillen.KTheory.Bass.SchemeIteratedSeedTransition
