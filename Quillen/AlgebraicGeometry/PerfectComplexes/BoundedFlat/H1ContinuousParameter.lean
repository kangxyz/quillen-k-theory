/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Path.ScalarRectangleConcatenation

/-! One continuous pure parameter family for original H1, glued along proved exact seams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.NativePathCells Quillen.ScalarRectangle
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Order

/-- The actual middle and reversed-polynomial cells are joined at their proved whole edge. -/
def secondTail : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  concatSecond middleParameter minusProductParameter.{u} (fun s ↦ (minus_middle_scalar s).symm)

theorem secondTail_lower (s t : unitInterval) :
    secondTail.{u} (s, lower t) = middleParameter (s, t) :=
  concatSecond_lower _ _ _ s t

theorem secondTail_upper (s t : unitInterval) :
    secondTail.{u} (s, upper t) = minusProductParameter.{u} (s, t) :=
  concatSecond_upper _ _ _ s t

theorem secondTail_zero (s : unitInterval) : secondTail.{u} (s, 0) = middleParameter (s, 0) :=
  concatSecond_zero _ _ _ s

theorem secondTail_one (s : unitInterval) :
    secondTail.{u} (s, 1) = minusProductParameter.{u} (s, 1) :=
  concatSecond_one _ _ _ s

theorem second_join (s : unitInterval) : plusProductParameter.{u} (s, 1) = secondTail.{u} (s, 0) :=
  (plus_middle_scalar s).trans (secondTail_zero s).symm

/-- The unchanged second half of H1 uses the original half, quarter, and quarter cylinder speeds. -/
def secondParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  concatSecond plusProductParameter.{u} secondTail.{u} second_join

theorem second_lower (s t : unitInterval) :
    secondParameter.{u} (s, lower t) = plusProductParameter.{u} (s, t) :=
  concatSecond_lower _ _ _ s t

theorem second_middle (s t : unitInterval) :
    secondParameter.{u} (s, upper (lower t)) = middleParameter (s, t) :=
  (concatSecond_upper _ _ _ s (lower t)).trans (secondTail_lower s t)

theorem second_upper (s t : unitInterval) :
    secondParameter.{u} (s, upper (upper t)) = minusProductParameter.{u} (s, t) :=
  (concatSecond_upper _ _ _ s (upper t)).trans (secondTail_upper s t)

theorem second_zero (s : unitInterval) :
    secondParameter.{u} (s, 0) = plusProductParameter.{u} (s, 0) :=
  concatSecond_zero _ _ _ s

theorem second_one (s : unitInterval) :
    secondParameter.{u} (s, 1) = minusProductParameter.{u} (s, 1) :=
  (concatSecond_one _ _ _ s).trans (secondTail_one s)

/-- The whole first/second seam follows from its three exact original parameter intervals. -/
theorem first_second_join (t : unitInterval) :
    firstParameter (1, t) = secondParameter.{u} (0, t) := by
  rcases three_cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact (first_plus_scalar r).trans (second_lower 0 r).symm
  · exact (first_middle_scalar r).trans (second_middle 0 r).symm
  · exact (first_minus_scalar r).trans (second_upper 0 r).symm

/-- The original entire H1 parameter is continuous, with all actual constituent speeds retained. -/
def h1Parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  concatFirst firstParameter secondParameter.{u} first_second_join

theorem h1_lower (s t : unitInterval) :
    h1Parameter.{u} (lower s, t) = firstParameter (s, t) :=
  concatFirst_lower _ _ _ s t

theorem h1_upper (s t : unitInterval) :
    h1Parameter.{u} (upper s, t) = secondParameter.{u} (s, t) :=
  concatFirst_upper _ _ _ s t

theorem h1_plus_cell (s t : unitInterval) :
    h1Parameter.{u} (upper s, lower t) = plusProductParameter.{u} (s, t) :=
  (h1_upper s (lower t)).trans (second_lower s t)

theorem h1_middle_cell (s t : unitInterval) :
    h1Parameter.{u} (upper s, upper (lower t)) = middleParameter (s, t) :=
  (h1_upper s (upper (lower t))).trans (second_middle s t)

theorem h1_minus_cell (s t : unitInterval) :
    h1Parameter.{u} (upper s, upper (upper t)) = minusProductParameter.{u} (s, t) :=
  (h1_upper s (upper (upper t))).trans (second_upper s t)

/-- Whole original H1/bottom scalar edge, with both original coordinates unchanged. -/
theorem h1_bottom_scalar (t : unitInterval) : h1Parameter.{u} (0, t) = bottomParameter.{u} (1, t) :=
  (concatFirst_zero _ _ _ t).trans (first_bottom_scalar t)

/-- Whole original positive H1/chart scalar edge, including the shared half-time point. -/
theorem h1_plus_scalar (s : unitInterval) : h1Parameter.{u} (s, 0) = plusParameter (1, s) := by
  rcases cover s with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact (h1_lower r 0).trans (first_old_plus_scalar r)
  · exact (h1_upper r 0).trans ((second_zero r).trans (product_old_plus_scalar r))

/-- The whole inverse chart edge retains the distinct inverse component and its original speeds. -/
theorem h1_minus_scalar (s : unitInterval) : h1Parameter.{u} (s, 1) = minusParameter (1, s) := by
  rcases cover s with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · exact (h1_lower r 1).trans (first_old_minus_scalar r)
  · exact (h1_upper r 1).trans ((second_one r).trans (product_old_minus_scalar r))

/-- The complete original H1 target edge is retained for the still-open whole M family. -/
theorem h1_one (t : unitInterval) : h1Parameter.{u} (1, t) = secondParameter.{u} (1, t) :=
  concatFirst_one _ _ _ t

end Quillen.PerfectComplexes.BassH1Order
