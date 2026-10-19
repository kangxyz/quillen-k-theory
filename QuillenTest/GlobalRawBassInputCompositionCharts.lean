/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCarrierCharts

/-! Exact whole-face regressions for original global input composition charts. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputCompositionCharts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The positive chart is a real square of the unchanged direct and successive comparisons. -/
def actualPositiveChart : InputCompositionCharts.ChartSquare f g
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (projection.app Z))
      (boundedFlatPerfectPrespectrumMap (projection.app Z))) :=
  InputCompositionCharts.plusChart f g

/-- The positive chart's direct face keeps every original input-comparison time. -/
theorem direct_boundary (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (actualPositiveChart f g).level n (0, (s, x)) =
      (plusSquareHomotopy (f ≫ g)).level n (s, x) :=
  (actualPositiveChart f g).at_zero n s x

/-- The Laurent edge is the original split composition under the actual comparison. -/
theorem laurent_boundary (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (actualPositiveChart f g).level n (r, (0, x)) =
      (InputCompositionCharts.laurentComposition f g).level n
        (r, (boundedFlatPerfectPrespectrumMap (plus.app Z)).map n x) :=
  (actualPositiveChart f g).left n r x

/-- The full top edge retains the actual span homotopy, including its terminal pause. -/
theorem span_boundary (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (actualPositiveChart f g).level n (r, (1, x)) =
      (comparison X).map n ((InputCompositionSpan.homotopy f g).level n
        (r, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z))).map n x)) :=
  (actualPositiveChart f g).right n r x

/-- The actual three-face carrier recovers every direct input cylinder value. -/
theorem original_input_face (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierCharts.inputFace f g) n ((s, t), x) =
      (inputComparisonHomotopy (f ≫ g)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) :=
  InputCompositionCarrierCharts.inputFace_native f g n s t x

/-- The whole positive carrier face retains the original chart under its actual polynomial map. -/
theorem positive_carrier_face (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierCharts.chartFace f g plus plus_projection) n ((r, s), x) =
      (InputCompositionCharts.plusChart f g).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) :=
  InputCompositionCarrierCharts.plusFace_native f g n r s x

/-- The independent inverse-coordinate chart is retained in the identical source carrier. -/
theorem negative_carrier_face (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily
      (InputCompositionCarrierCharts.source f g)
      (InputCompositionCarrierCharts.chartFace f g minus minus_projection) n ((r, s), x) =
      (InputCompositionCharts.minusChart f g).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app Z)).map n x)) :=
  InputCompositionCarrierCharts.minusFace_native f g n r s x

/-- All native chart times are independent of the prespectrum structure coordinate. -/
theorem independent_structure (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    (actualPositiveChart f g).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen
        (polynomial.obj Z))).structureMap n x t)) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        ((actualPositiveChart f g).level n (r, (s, x))) t :=
  (actualPositiveChart f g).comm n r s x t

/-- The positive fixed-scheme chart pair consumes no supplied comparison square. -/
def positiveProjectionChart (X : Scheme.{u}) :=
  InputCompositionCharts.plusChart (plus.app X) (projection.app X)

/-- The inverse fixed-scheme pair retains its different original inner chart arrow. -/
def inverseProjectionChart (X : Scheme.{u}) :=
  InputCompositionCharts.minusChart (minus.app X) (projection.app X)

end QuillenTest.GlobalRawBassInputCompositionCharts
