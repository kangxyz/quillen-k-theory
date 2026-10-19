/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMovingSquarePause

/-!
# Full native chart-composition surfaces on the original geometric simplex

The actual scheme-transformation rectangle is lifted through all eighteen original dependent
nodes. Its boundary rotation, three-side collapse and terminal pause use the unchanged scalar
clocks, at every native level and input point. Only pure scalar words and generic geometric
rectangle lift lemmas are reused from the coefficient development.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionChartNative
variable {M N : Scheme.{u} ⥤ Scheme.{u}} (α : N ⟶ M)
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- All original geometric rectangle vertices and reference isomorphisms in one simplex. -/
def simplex := DoubleSquareMergedSimplex.simplex
  (M.map g) (M.map f) (N.map g) (N.map f)
  (α.app Z) (α.app Y) (α.app X)
  (α.naturality g).symm (α.naturality f).symm

/-- The entire actual rectangle uses the existing original scalar comparison parameter. -/
theorem rectangle_nativeLift :
    HomotopyLift (simplex α f g) DoubleSquareScalarPaths.rectangleParameter
      (InputCompositionTransformations.rectangle α f g) :=
  DoubleSquareScalarPaths.original_rectangle_nativeLift
    (M.map g) (M.map f) (N.map g) (N.map f)
    (α.app Z) (α.app Y) (α.app X)
    (α.naturality g).symm (α.naturality f).symm

/-- Reversing the original rectangle retains its full time coordinate and endpoint casts. -/
theorem comparison_nativeLift :
    HomotopyLift (simplex α f g) DoubleSquareScalarPaths.originalComparisonParameter
      (InputCompositionTransformations.comparison α f g) := by
  intro n r s x
  exact (HomotopyLift.symmPath _ (rectangle_nativeLift α f g)) n r s x

open DoubleSquareScalarPaths

/-- The target geometric composition retains its exact original time. -/
theorem targetTrack_path :
    PathLift (simplex α f g) targetChart
      (InputCompositionTransformations.targetTrack α f g) := by
  let S := simplex α f g
  change PathLift S targetChart
    (InputCompositionTransformations.targetTrack α f g)
  have h := HomotopyLift.target S (comparison_nativeLift α f g)
  have h' := PathLift.trans_left S h
  intro n t x
  have hv := (PathLift.trans_left S h') n (unitInterval.symm t) x
  change prespectrumSimplexFamily S n
      (targetChart (unitInterval.symm (unitInterval.symm t)), x) =
    (InputCompositionTransformations.targetTrack α f g).level n
      (unitInterval.symm (unitInterval.symm t), x) at hv
  rw [unitInterval.symm_symm] at hv
  exact hv

/-- The original source composition retains its exact original time. -/
theorem sourceTrack_path :
    PathLift (simplex α f g) sourceChart
      (InputCompositionTransformations.sourceTrack α f g) := by
  let S := simplex α f g
  have h := HomotopyLift.target S (comparison_nativeLift α f g)
  exact PathLift.trans_right S h

/-- The direct outer geometric square retains its exact original time. -/
theorem outerSquare_path :
    PathLift (simplex α f g) outerSquarePath
      (InputCompositionTransformations.square α (f ≫ g)) := by
  let S := simplex α f g
  have h := HomotopyLift.target S (comparison_nativeLift α f g)
  exact PathLift.trans_right S (PathLift.trans_left S h)

/-- Both successive geometric squares are one exact scalar route. -/
theorem compositeSquare_path :
    PathLift (simplex α f g) originalComparisonSource
      (InputCompositionTransformations.compositeSquare α f g) :=
  HomotopyLift.source _ (comparison_nativeLift α f g)

/-- The complete actual boundary rotation retains the original scalar word. -/
theorem boundary_nativeLift :
    HomotopyLift (simplex α f g)
      DoubleSquareScalarPaths.coefficientBoundaryParameter
      (InputCompositionTransformations.boundary α f g) := by
  exact HomotopyLift.boundaryOfComparison (simplex α f g)
    (targetTrack_path α f g) (outerSquare_path α f g) (sourceTrack_path α f g)
    (comparison_nativeLift α f g)

/-- The full moving square uses the unchanged original three-side collapse parameter. -/
theorem movingSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (M.obj Z))).space n) :
    prespectrumSimplexFamily (simplex α f g) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
      (InputCompositionTransformations.movingSquare α f g).level n (r, (s, x)) :=
  HomotopyLift.toSquare _ (boundary_nativeLift α f g) n r s x

/-- The native terminal pause is preserved on the entire original chart surface. -/
theorem pausedSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (M.obj Z))).space n) :
    prespectrumSimplexFamily (simplex α f g) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      ((InputCompositionTransformations.movingSquare α f g).pauseRight).level n
        (r, (s, x)) :=
  HomotopyLift.pauseRight_square _ (boundary_nativeLift α f g)
    (targetTrack_path α f g) (compositeSquare_path α f g) (sourceTrack_path α f g) n r s x

/-- Every original positive chart value is recovered, with both coordinates independent. -/
theorem plusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    prespectrumSimplexFamily (simplex plus f g) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      (InputCompositionCharts.plusChart f g).level n (r, (s, x)) :=
  pausedSquare_native plus f g n r s x

/-- The separate inverse chart keeps its actual natural transformation and scalar time. -/
theorem minusChart_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj Z))).space n) :
    prespectrumSimplexFamily (simplex minus f g) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      (InputCompositionCharts.minusChart f g).level n (r, (s, x)) :=
  pausedSquare_native minus f g n r s x

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionChartNative
