/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Bass.NaturalTrack
public import Quillen.KTheory.Bass.GeometricSeedCospan
public import Quillen.Topology.Prespectrum.NullLoopNaturality

/-! # The original all-scheme seed for a natural Laurent track -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSquareInterchange
open GeometricSeedCospan SquareConeStrength
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

/-- The original whole null/unit/null seed, using the actual geometric diagonal. -/
def seed (A : Track laurent.op coefficient F) :
    F ⟶ (strictDiagramFunctor squareFunctor).obj F :=
  WholeSeedCospan.seed (geometricSquare F) (sourceTrack F A.homotopy)
    (sourceTrack_naturality F A.homotopy A.naturality)

/-- A local whole-track intertwiner preserves the original all-scheme seed. -/
theorem seed_square (A : Track laurent.op coefficient F)
    (B : Track laurent.op coefficient G) (η : F ⟶ G) (hη : Equivariant A B η) :
    seed A ≫ (strictDiagramFunctor squareFunctor).map η = η ≫ seed B := by
  apply NatTrans.ext
  funext X
  change (((sourceTrack F A.homotopy X).postcomp
      (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (square X)))))
      |>.nullLoopMap (StrictSquare.sourceNullHomotopy
        (F.mapArrow.mapArrow.obj (square X)))) ≫
    parameterLoopingMap ((ConeTrack.map squareFunctor η).app X) = _
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (mappingConeInclusion (StrictSquare.comparison
        (G.mapArrow.mapArrow.obj (square X)))).map n
      ((η.app (laurent.op.obj X)).map n ((A.homotopy X).level n (r, x))) =
      (mappingConeInclusion (StrictSquare.comparison
        (G.mapArrow.mapArrow.obj (square X)))).map n
      ((B.homotopy X).level n (r, (η.app X).map n x))
    exact congrArg _ (congrArg (fun k => k.map n x) (hη X r)).symm
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact StrictSquare.sourceNullHomotopy_naturality_apply
      (diagramSquareMap η (square X)) n r x

end Quillen.KTheory.Bass.SchemeNaturalSeed
