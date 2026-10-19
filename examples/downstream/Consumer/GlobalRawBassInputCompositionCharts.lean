/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierCharts

/-! Independent consumers of actual original composition chart faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
universe u
namespace Consumer.GlobalRawBassInputCompositionCharts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A downstream caller obtains the complete positive chart without coherence hypotheses. -/
def positiveChart : InputCompositionCharts.ChartSquare f g
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (projection.app Z))
      (boundedFlatPerfectPrespectrumMap (projection.app Z))) :=
  InputCompositionCharts.plusChart f g

/-- The original direct face is recovered at every native point and comparison time. -/
theorem original_direct (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (positiveChart f g).level n (0, (s, x)) =
      (plusSquareHomotopy (f ≫ g)).level n (s, x) :=
  (positiveChart f g).at_zero n s x

/-- The full independent inverse carrier face is the originally specified chart square. -/
theorem inverse_face (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierCharts.chartFace f g minus minus_projection) n ((r, s), x) =
      (InputCompositionCharts.minusChart f g).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) :=
  InputCompositionCarrierCharts.minusFace_native f g n r s x

end Consumer.GlobalRawBassInputCompositionCharts
