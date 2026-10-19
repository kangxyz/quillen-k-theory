/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopVertex

/-! The entire original vertex stage and its independent native structure time. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace QuillenTest.GlobalRawBassInputCompositionTopVertex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Every original overlap height recovers M at its whole first-half clock. -/
theorem whole_vertex (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTopVertex.face f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) :=
  InputCompositionTopVertex.face_native f g n r t x

/-- The same complete carrier face keeps a separately varying prespectrum structure coordinate. -/
theorem structure_time (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTopVertex.face f g) (n + 1)
        ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
          (InputCompositionTopVertex.face f g) n ((r, t), x)) z :=
  InputCompositionTopVertex.face_structure f g n r t z x

/-- The two actual internal carrier seams are simultaneously exact, before evaluation. -/
theorem internal_seams (r : unitInterval) :
    (InputCompositionTopPieces.movingFace f g plus plus_projection (r, 1),
      InputCompositionTopPieces.movingFace f g minus minus_projection (r, 1)) =
    (InputCompositionTopPieces.middleFace f g (r, 0),
      InputCompositionTopPieces.middleFace f g (r, 1)) :=
  Prod.ext (InputCompositionTopVertex.plus_middle f g r)
    (InputCompositionTopVertex.minus_middle f g r)

end QuillenTest.GlobalRawBassInputCompositionTopVertex
