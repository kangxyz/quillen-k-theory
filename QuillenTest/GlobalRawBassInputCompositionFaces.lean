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

/-! Whole original bottom and M vertex-piece regressions, without carrier seam assertions. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace QuillenTest.GlobalRawBassInputCompositionFaces
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Every value is the original Laurent track on the whole original Bass cylinder. -/
theorem original_bottom (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.face f g) n ((r, t), x) =
      (InputCompositionCharts.laurentTrack f g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) :=
  InputCompositionCarrierBottom.face_native f g n r t x

/-- The initial native edge retains the direct Laurent-map composition, at every Bass height. -/
theorem direct_native_edge (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.face f g) n ((0, t), x) =
      (boundedFlatPerfectPrespectrumMap (laurent.map (f ≫ g))).map n
        ((squareHomotopy Z).level n (t, x)) :=
  (original_bottom f g n 0 t x).trans ((InputCompositionCharts.laurentTrack f g).at_zero n _)

/-- The final native edge retains the two original Laurent maps in contravariant order. -/
theorem composite_native_edge (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierBottom.face f g) n ((1, t), x) =
      (boundedFlatPerfectPrespectrumMap (laurent.map f)).map n
        ((boundedFlatPerfectPrespectrumMap (laurent.map g)).map n
          ((squareHomotopy Z).level n (t, x))) :=
  (original_bottom f g n 1 t x).trans ((InputCompositionCharts.laurentTrack f g).at_one n _)

/-- The source transport retains the exact original scheme map, rather than a model replacement. -/
theorem actual_total :
    (laurent.map f ≫ laurent.map g) ≫ (plus.app Z ≫ projection.app Z) =
      laurent.map (f ≫ g) ≫ laurentProjection.app Z :=
  InputCompositionCarrierBottom.total f g

open Quillen.NativePathCells

/-- The complete positive piece is the actual first-half M cylinder at its original half clock. -/
theorem plus_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTopPieces.movingFace f g plus plus_projection) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (lower t, x)) :=
  InputCompositionTopPieces.plus_top_cell f g n r t x

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

/-- The inverse piece retains the original reversed square and final-quarter M height. -/
theorem minus_top_cell (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionTopPieces.movingFace f g minus minus_projection) n ((r, unitInterval.symm t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (upper (upper t), x)) :=
  InputCompositionTopPieces.minus_top_cell f g n r t x

end QuillenTest.GlobalRawBassInputCompositionFaces
