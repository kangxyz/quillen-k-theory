/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.HomotopyPathSlice
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeC1OldInitialPasteSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Conjugation

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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeC1WholeOldSeedSeam
open CoefficientBassCompositeJ0ConeBoundaries CoefficientBassCompositeJ0Rectangles
open CoefficientBassCompositeJ0PairedNull CoefficientBassCompositeJ0TypedUnitRails
open CoefficientBassPositiveC1SeedFace
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The ordinary corrected square keeps the entire original lower path. -/
theorem corrected_minus_zero (s : I) :
    correctedMinus P p q (s, 0) =
      ((positiveMovementMinus P p q).trans (oldConeMinus P p q)) s := by
  change (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P
    p q).parameter (0, s) = _
  exact ((CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P
    p q).at_zero s).trans
      (CoefficientBassCompositeC1OldInitialPasteSeam.initial_minus P p q s)

/-- The shifted corrected square retains its own full lower path and plus tip. -/
theorem corrected_plus_zero (s : I) :
    correctedPlus P p q (s, 0) =
      ((positiveMovementPlus P p q).trans (oldConePlus P p q)) s := by
  change (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P
    p q).parameter (0, s) = _
  exact ((CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P
    p q).at_zero s).trans
      (CoefficientBassCompositeC1OldInitialPasteSeam.initial_plus P p q s)

/-- Literal ordinary null concatenation, including the nested movement/cone halves. -/
theorem null_minus_zero (s : I) :
    nullMinus P p q (s, 0) = oldNullMinus P p q s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (positiveMinus P p q)
    (correctedMinus P p q) id 0
    (oldPositiveMinus P p q) ((positiveMovementMinus P p q).trans (oldConeMinus P p q))
    (CoefficientBassCompositeC1OldSourceRails.positive_minus P p q)
    (corrected_minus_zero P p q) s

/-- Literal shifted null concatenation, with the separate shifted reference and endpoint. -/
theorem null_plus_zero (s : I) :
    nullPlus P p q (s, 0) = oldNullPlus P p q s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (positivePlus P p q)
    (correctedPlus P p q) id 0
    (oldPositivePlus P p q) ((positiveMovementPlus P p q).trans (oldConePlus P p q))
    (CoefficientBassCompositeC1OldSourceRails.positive_plus P p q)
    (corrected_plus_zero P p q) s

/-- The unit and shifted null retain their original right-associated half clocks. -/
theorem unit_null_zero (s : I) :
    ((forwardUnit P p q).trans
      (nullPlus P p q)) (s, 0) =
        ((oldUnit P p q).trans (oldNullPlus P p q)) s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (forwardUnit P p q)
    (nullPlus P p q) id 0
    (oldUnit P p q) (oldNullPlus P p q)
    (CoefficientBassCompositeC1OldSourceRails.unit P p q)
    (null_plus_zero P p q) s

/-- Whole carrier equality at the original seed clock, before native evaluation. -/
theorem face_zero (s : I) :
    face P p q (0, s) =
      CoefficientBassCompositeJ0Conjugation.sourceWord P p q s :=
  ContinuousMap.Homotopy.PathSlice.trans
    (nullMinus P p q).symm
    ((forwardUnit P p q).trans
      (nullPlus P p q)) id 0
    (oldNullMinus P p q).symm ((oldUnit P p q).trans (oldNullPlus P p q))
    (ContinuousMap.Homotopy.PathSlice.symm (nullMinus P p q) id 0
      (oldNullMinus P p q) (null_minus_zero P p q)) (unit_null_zero P p q) s

/-- The original J0 exit and C1 entrance agree for every carrier seed coordinate. -/
theorem reverseComparison_exit (s : I) :
    CoefficientBassCompositeJ0Conjugation.reverseComparison P p q (1, s) =
      face P p q (0, s) :=
  ((CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).apply_one s).trans
    (face_zero P p q s).symm

end Quillen.PerfectComplexes.CoefficientBassCompositeC1WholeOldSeedSeam
