/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierTop

/-! The whole original composition M face, its clocks and independent structure time. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInputCompositionCarrierTop
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Every original composition time and overlap height recovers the entire prescribed M. -/
theorem whole_face (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierTop.face f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) :=
  InputCompositionCarrierTop.face_native f g n r t x

/-- The same complete carrier face keeps a separately varying prespectrum structure coordinate. -/
theorem structure_time (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierTop.face f g) (n + 1)
        ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
          (InputCompositionCarrierTop.face f g) n ((r, t), x)) z :=
  InputCompositionCarrierTop.face_structure f g n r t z x

/-- Both original outer stages remain visible before native evaluation. -/
theorem stage_clocks (r t : unitInterval) :
    (InputCompositionCarrierTop.face f g (lower r, t),
      InputCompositionCarrierTop.face f g (upper r, t)) =
    (InputCompositionTopVertex.face f g (r, t),
      InputCompositionTopWord.reassociation f g (unitInterval.symm r, t)) :=
  Prod.ext (InputCompositionCarrierTop.face_lower f g r t)
    (InputCompositionCarrierTop.face_upper f g r t)

end Consumer.GlobalRawBassInputCompositionCarrierTop
