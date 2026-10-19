/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierBottom
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopPieces

/-! Independent consumers of the original bottom and M middle-piece carrier values. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInputCompositionFaces
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- All original bottom-face parameters are recovered without supplied composition coherence. -/
theorem original_face (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.face f g) n ((r, t), x) =
      (InputCompositionCharts.laurentTrack f g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) :=
  InputCompositionCarrierBottom.face_native f g n r t x

open Quillen.NativePathCells

/-- The entire middle piece keeps the original independent M clock and middle-quarter height. -/
theorem middle_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTopPieces.middleFace f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (lower t), x)) :=
  InputCompositionTopPieces.middle_top_cell f g n r t x

end Consumer.GlobalRawBassInputCompositionFaces
