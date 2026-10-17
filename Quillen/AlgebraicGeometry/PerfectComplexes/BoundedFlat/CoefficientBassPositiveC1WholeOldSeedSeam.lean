/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.HomotopyPathSlice
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldPositiveSourceRails
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldUnitSourceRail
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldInitialPasteSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0Conjugation

/-!
# The whole old seed is the initial C1 carrier path

Full carrier rail equalities are pasted with their literal nested half clocks. The minus and
plus tips remain distinct. No native evaluation or terminal cross-route equality is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1WholeOldSeedSeam
open CoefficientBassPositiveJ0ConeBoundaries CoefficientBassPositiveJ0Rectangles
open CoefficientBassPositiveJ0PairedNull CoefficientBassPositiveJ0TypedUnitRails
open CoefficientBassPositiveC1SeedFace
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The ordinary corrected square keeps the entire original lower path. -/
theorem corrected_minus_zero (s : I) :
    correctedMinus P (firstArrow d) (secondArrow d) (s, 0) =
      ((positiveMovementMinus P d).trans (oldConeMinus P d)) s := by
  change (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P
    (firstArrow d) (secondArrow d)).parameter (0, s) = _
  exact ((CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P
    (firstArrow d) (secondArrow d)).at_zero s).trans
      (CoefficientBassPositiveC1OldInitialPasteSeam.initial_minus P d s)

/-- The shifted corrected square retains its own full lower path and plus tip. -/
theorem corrected_plus_zero (s : I) :
    correctedPlus P (firstArrow d) (secondArrow d) (s, 0) =
      ((positiveMovementPlus P d).trans (oldConePlus P d)) s := by
  change (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P
    (firstArrow d) (secondArrow d)).parameter (0, s) = _
  exact ((CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P
    (firstArrow d) (secondArrow d)).at_zero s).trans
      (CoefficientBassPositiveC1OldInitialPasteSeam.initial_plus P d s)

/-- Literal ordinary null concatenation, including the nested movement/cone halves. -/
theorem null_minus_zero (s : I) :
    nullMinus P (firstArrow d) (secondArrow d) (s, 0) = oldNullMinus P d s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (positiveMinus P (firstArrow d) (secondArrow d))
    (correctedMinus P (firstArrow d) (secondArrow d)) id 0
    (oldPositiveMinus P d) ((positiveMovementMinus P d).trans (oldConeMinus P d))
    (CoefficientBassPositiveC1OldPositiveSourceRails.actual_source_minus P d)
    (corrected_minus_zero P d) s

/-- Literal shifted null concatenation, with the separate shifted reference and endpoint. -/
theorem null_plus_zero (s : I) :
    nullPlus P (firstArrow d) (secondArrow d) (s, 0) = oldNullPlus P d s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (positivePlus P (firstArrow d) (secondArrow d))
    (correctedPlus P (firstArrow d) (secondArrow d)) id 0
    (oldPositivePlus P d) ((positiveMovementPlus P d).trans (oldConePlus P d))
    (CoefficientBassPositiveC1OldPositiveSourceRails.actual_source_plus P d)
    (corrected_plus_zero P d) s

/-- The unit and shifted null retain their original right-associated half clocks. -/
theorem unit_null_zero (s : I) :
    ((forwardUnit P (firstArrow d) (secondArrow d)).trans
      (nullPlus P (firstArrow d) (secondArrow d))) (s, 0) =
        ((oldUnit P d).trans (oldNullPlus P d)) s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (forwardUnit P (firstArrow d) (secondArrow d))
    (nullPlus P (firstArrow d) (secondArrow d)) id 0
    (oldUnit P d) (oldNullPlus P d)
    (CoefficientBassPositiveC1OldUnitSourceRail.actual_old_unit P d)
    (null_plus_zero P d) s

/-- Whole carrier equality at the original seed clock, before native evaluation. -/
theorem face_zero (s : I) :
    face P (firstArrow d) (secondArrow d) (0, s) =
      CoefficientBassPositiveJ0Conjugation.sourceWord P d s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (nullMinus P (firstArrow d) (secondArrow d)).symm
    ((forwardUnit P (firstArrow d) (secondArrow d)).trans
      (nullPlus P (firstArrow d) (secondArrow d))) id 0
    (oldNullMinus P d).symm ((oldUnit P d).trans (oldNullPlus P d))
    (ContinuousMap.Homotopy.PathSlice.symm (nullMinus P (firstArrow d) (secondArrow d)) id 0
      (oldNullMinus P d) (null_minus_zero P d)) (unit_null_zero P d) s

/-- The original J0 exit and C1 entrance agree for every carrier seed coordinate. -/
theorem reverseComparison_exit (s : I) :
    CoefficientBassPositiveJ0Conjugation.reverseComparison P d (1, s) =
      face P (firstArrow d) (secondArrow d) (0, s) :=
  ((CoefficientBassPositiveJ0Conjugation.reverseComparison P d).apply_one s).trans
    (face_zero P d s).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveC1WholeOldSeedSeam
