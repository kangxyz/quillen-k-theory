/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Path.ScalarRectangleConcatenation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductStrips
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1CorrectedBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1ShiftedCorrectedBoundary

/-! The literal five-branch C1 carrier face, with two distinct endpoints. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open Quillen.NativePathCells Quillen.ScalarRectangle
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFace
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveC1SourceProductStrips
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The ordinary positive start curve, with composition time as its parameter. -/
def ordinaryStart : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (positiveParameter P p q (r, 0)), by fun_prop⟩
/-- The shifted positive start curve retains the actual common-unit action. -/
def shiftedStart : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (shiftedPositiveParameter P p q (r, 0)), by fun_prop⟩
/-- The ordinary product end curve. -/
def ordinaryEnd : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (positiveParameter P p q (r, 1)), by fun_prop⟩
/-- The shifted product end curve. -/
def shiftedEnd : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (shiftedPositiveParameter P p q (r, 1)), by fun_prop⟩

/-- Whole ordinary product-to-corrected-square seam, before evaluation. -/
theorem ordinary_seam (r : I) :
    ordinaryEnd P p q r =
      (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).parameter (r, 0) := by
  rw [(CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).left]
  exact congrArg (includeLaurent P p q) (positive_chart_seam P p q r)

/-- Whole shifted seam, with the independent plus-cylinder attachment. -/
theorem shifted_seam (r : I) :
    shiftedEnd P p q r =
      (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).parameter
        (r, 0) := by
  rw [(CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).left]
  exact congrArg (includeLaurent P p q) (shifted_positive_chart_seam P p q r)

/-- Positive path time is first; composition time remains the domain coordinate. -/
def positiveMinus : (ordinaryStart P p q).Homotopy (ordinaryEnd P p q) where
  toFun z := includeLaurent P p q (positiveParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl
/-- The separately shifted positive strip. -/
def positivePlus : (shiftedStart P p q).Homotopy (shiftedEnd P p q) where
  toFun z := includeLaurent P p q (shiftedPositiveParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The whole original ordinary corrected null square, ending at its own tip. -/
def correctedMinus : (ordinaryEnd P p q).Homotopy (ContinuousMap.const I (minusTip P p q)) where
  toFun z := (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).parameter
    (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (ordinary_seam P p q r).symm
  map_one_left r := (CoefficientBassPositiveC1CorrectedBoundary.correctedSquare P p q).right r
/-- The shifted corrected null square ends at the distinct plus tip. -/
def correctedPlus : (shiftedEnd P p q).Homotopy (ContinuousMap.const I (plusTip P p q)) where
  toFun z :=
    (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).parameter
      (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (shifted_seam P p q r).symm
  map_one_left r :=
    (CoefficientBassPositiveC1ShiftedCorrectedBoundary.correctedSquare P p q).right r

/-- Both unit endpoint joins are the full reference-bearing product equalities. -/
def forwardUnit : (ordinaryStart P p q).Homotopy (shiftedStart P p q) where
  toFun z := includeLaurent P p q (unitParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left r := congrArg (includeLaurent P p q) (unit_lower P p q r)
  map_one_left r := congrArg (includeLaurent P p q) (unit_upper P p q r)

/-- The ordinary null retains its original two halves. -/
def nullMinus := (positiveMinus P p q).trans (correctedMinus P p q)
/-- The shifted null retains its own reference and tip. -/
def nullPlus := (positivePlus P p q).trans (correctedPlus P p q)
/-- Literal original null inverse, unit, null word. -/
def seedWord : (ContinuousMap.const I (minusTip P p q)).Homotopy
    (ContinuousMap.const I (plusTip P p q)) :=
  (nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))
/-- A jointly continuous carrier face, with composition time first. -/
def face : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ seedWord P p q (z.2, z.1), by fun_prop⟩

/-- The entire literal boundary word, without a change of parentheses. -/
theorem face_word (r s : I) : face P p q (r, s) =
    ((nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))) (s, r) := rfl
/-- The carrier source endpoint is the minus tip. -/
theorem face_bottom (r : I) : face P p q (r, 0) = minusTip P p q :=
  (seedWord P p q).apply_zero r
/-- The carrier target endpoint is the separate plus tip. -/
theorem face_top (r : I) : face P p q (r, 1) = plusTip P p q :=
  (seedWord P p q).apply_one r

private theorem symm_lower (t : I) : unitInterval.symm (lower t) =
    upper (unitInterval.symm t) := by
  apply Subtype.ext
  change 1 - (t : ℝ) / 2 = (1 - (t : ℝ) + 1) / 2
  ring
private theorem symm_upper (t : I) : unitInterval.symm (upper t) =
    lower (unitInterval.symm t) := by
  apply Subtype.ext
  change 1 - ((t : ℝ) + 1) / 2 = (1 - (t : ℝ)) / 2
  ring

/-- First quarter: corrected ordinary square at the reversed original path time. -/
theorem face_first (r t : I) : face P p q (r, lower (lower t)) =
    correctedMinus P p q (unitInterval.symm t, r) := by
  change (seedWord P p q) (lower (lower t), r) = _
  rw [seedWord, homotopy_lower]
  change nullMinus P p q (unitInterval.symm (lower t), r) = _
  rw [symm_lower, nullMinus, homotopy_upper]
/-- Second quarter: positive ordinary strip at reversed path time. -/
theorem face_second (r t : I) : face P p q (r, lower (upper t)) =
    positiveMinus P p q (unitInterval.symm t, r) := by
  change (seedWord P p q) (lower (upper t), r) = _
  rw [seedWord, homotopy_lower]
  change nullMinus P p q (unitInterval.symm (upper t), r) = _
  rw [symm_upper, nullMinus, homotopy_lower]
/-- Middle quarter: the source unit at its unchanged forward time. -/
theorem face_third (r t : I) : face P p q (r, upper (lower t)) =
    forwardUnit P p q (t, r) := by
  change (seedWord P p q) (upper (lower t), r) = _
  rw [seedWord, homotopy_upper, homotopy_lower]
/-- Seventh eighth: the shifted positive strip at forward time. -/
theorem face_fourth (r t : I) : face P p q (r, upper (upper (lower t))) =
    positivePlus P p q (t, r) := by
  change (seedWord P p q) (upper (upper (lower t)), r) = _
  rw [seedWord, homotopy_upper, homotopy_upper, nullPlus, homotopy_lower]
/-- Final eighth: the shifted corrected square with its distinct tip. -/
theorem face_fifth (r t : I) : face P p q (r, upper (upper (upper t))) =
    correctedPlus P p q (t, r) := by
  change (seedWord P p q) (upper (upper (upper t)), r) = _
  rw [seedWord, homotopy_upper, homotopy_upper, nullPlus, homotopy_upper]

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFace
