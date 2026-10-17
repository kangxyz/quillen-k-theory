/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftComparisons
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftTerminalSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftStartingSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualRightRoute

/-! The actual left carrier route, with the original two reversed comparison halves. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveActualLeftRoute
open CoefficientBassPositiveLeftComparisons CoefficientBassPositiveLeftPairedNull
open CoefficientBassPositiveLeftUnitPasting CoefficientBassPositiveLeftRectangles
open CoefficientBassPositiveJ0ConeBoundaries
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Rebased first-new nulls retain exactly the midpoint null values. -/
theorem first_new_null (e : Bool) (s : I) : firstNewNull P p q e s =
    CoefficientBassPositiveLeftMidpointSeed.firstFullNull P p q e s := rfl

/-- Rebased middle-old nulls retain the original three-piece midpoint word. -/
theorem middle_old_null (e : Bool) (s : I) : middleOldNull P p q e s =
    CoefficientBassPositiveLeftMidpointSeed.middleFullNull P p q e s := rfl

/-- Rebased first-old nulls retain the entire terminal D/L/A word. -/
theorem first_old_null (e : Bool) (s : I) : firstOldNull P p q e s =
    CoefficientBassPositiveLeftTerminalNull.oldNull P p q e s := rfl

/-- Rebased middle-new nulls retain the starting K/Q-cylinder word. -/
theorem middle_new_null (e : Bool) (s : I) : middleNewNull P p q e s =
    CoefficientBassPositiveLeftStartingSeed.newNull P p q e s := rfl

/-- The first target is the previously constructed complete midpoint seed. -/
theorem first_target_seed (s : I) : firstTargetWord P p q s =
    CoefficientBassPositiveLeftMidpointSeed.firstNewSeed P p q s :=
  map_trans_values id (firstNewNull P p q false).symm
    ((firstNewUnit P p q).trans (firstNewNull P p q true))
    (CoefficientBassPositiveLeftMidpointSeed.firstFullNull P p q false).symm
    ((CoefficientBassPositiveLeftMidpointSeed.firstUnit P p q).trans
      (CoefficientBassPositiveLeftMidpointSeed.firstFullNull P p q true))
    (fun t ↦ first_new_null P p q false (unitInterval.symm t))
    (map_trans_values id _ _ _ _ (fun _ ↦ rfl) (first_new_null P p q true)) s

/-- The middle source is the previously constructed complete midpoint seed. -/
theorem middle_source_seed (s : I) : middleSourceWord P p q s =
    CoefficientBassPositiveLeftMidpointSeed.middleOldSeed P p q s :=
  map_trans_values id (middleOldNull P p q false).symm
    ((middleOldUnit P p q).trans (middleOldNull P p q true))
    (CoefficientBassPositiveLeftMidpointSeed.middleFullNull P p q false).symm
    ((CoefficientBassPositiveLeftMidpointSeed.middleUnit P p q).trans
      (CoefficientBassPositiveLeftMidpointSeed.middleFullNull P p q true))
    (fun t ↦ middle_old_null P p q false (unitInterval.symm t))
    (map_trans_values id _ _ _ _ (fun _ ↦ rfl) (middle_old_null P p q true)) s

/-- The first source is the entire terminal seed, with unchanged inverse/trans nesting. -/
theorem first_source_seed (s : I) : firstSourceWord P p q s =
    CoefficientBassPositiveLeftTerminalSeed.terminalSeed P p q s :=
  map_trans_values id (firstOldNull P p q false).symm
    ((firstOldUnit P p q).trans (firstOldNull P p q true))
    (CoefficientBassPositiveLeftTerminalNull.oldNull P p q false).symm
    ((CoefficientBassPositiveLeftTerminalUnit.firstOldUnit P p q).trans
      (CoefficientBassPositiveLeftTerminalNull.oldNull P p q true))
    (fun t ↦ first_old_null P p q false (unitInterval.symm t))
    (map_trans_values id _ _ _ _ (fun _ ↦ rfl) (first_old_null P p q true)) s

/-- The middle target is the entire starting seed, before any native evaluation. -/
theorem middle_target_seed (s : I) : middleTargetWord P p q s =
    CoefficientBassPositiveLeftStartingSeed.startingSeed P p q s :=
  map_trans_values id (middleNewNull P p q false).symm
    ((middleNewUnit P p q).trans (middleNewNull P p q true))
    (CoefficientBassPositiveLeftStartingSeed.newNull P p q false).symm
    ((CoefficientBassPositiveLeftStartingSeed.newUnit P p q).trans
      (CoefficientBassPositiveLeftStartingSeed.newNull P p q true))
    (fun t ↦ middle_new_null P p q false (unitInterval.symm t))
    (map_trans_values id _ _ _ _ (fun _ ↦ rfl) (middle_new_null P p q true)) s

/-- Both comparison constituents meet as complete carrier words, not only at their endpoints. -/
theorem midpoint (s : I) : middleSourceWord P p q s = firstTargetWord P p q s :=
  (middle_source_seed P p q s).trans
    ((CoefficientBassPositiveLeftMidpointSeed.midpoint_seed_parameter P p q s).symm.trans
      (first_target_seed P p q s).symm)

variable (d : Under R)

/-- The common midpoint is the whole first-target seed. -/
def middlePath : C(I, CoefficientBassPositiveJ0Rectangles.Carrier P d) :=
  (firstTargetWord P (firstArrow d) (secondArrow d)).toContinuousMap

/-- Reverse the middle comparison exactly once, retaining its own full seed coordinate. -/
def middle : (CoefficientBassPositiveActualRightRoute.start P d).Homotopy (middlePath P d) where
  toFun z := middleComparison P (firstArrow d) (secondArrow d) (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact ((middleComparison P (firstArrow d) (secondArrow d)).apply_one s).trans
      ((middle_target_seed P (firstArrow d) (secondArrow d) s).trans
        (CoefficientBassPositiveLeftStartingSeed.starting_seed_target P
          (firstArrow d) (secondArrow d) s))
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((middleComparison P (firstArrow d) (secondArrow d)).apply_zero s).trans
      (midpoint P (firstArrow d) (secondArrow d) s)

/-- Reverse the first comparison exactly once and use its proved entire terminal seed. -/
def first : (middlePath P d).Homotopy (CoefficientBassPositiveActualRightRoute.finish P d) where
  toFun z := firstComparison P (firstArrow d) (secondArrow d) (unitInterval.symm z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left s := by
    rw [unitInterval.symm_zero]
    exact (firstComparison P (firstArrow d) (secondArrow d)).apply_one s
  map_one_left s := by
    rw [unitInterval.symm_one]
    exact ((firstComparison P (firstArrow d) (secondArrow d)).apply_zero s).trans
      ((first_source_seed P (firstArrow d) (secondArrow d) s).trans
        (CoefficientBassPositiveLeftTerminalSeed.terminal_parameter P
          (firstArrow d) (secondArrow d) s))

/-- The original outer order: reversed middle on the first half, reversed first on the second. -/
def routeHomotopy : (CoefficientBassPositiveActualRightRoute.start P d).Homotopy
    (CoefficientBassPositiveActualRightRoute.finish P d) := (middle P d).trans (first P d)

/-- The actual left route is jointly continuous in original route and seed time. -/
def route : C(I × I, CoefficientBassPositiveJ0Rectangles.Carrier P d) :=
  (routeHomotopy P d).toContinuousMap

theorem route_start (s : I) : route P d (0, s) =
    CoefficientBassPositiveActualRightRoute.start P d s := (routeHomotopy P d).apply_zero s

theorem route_finish (s : I) : route P d (1, s) =
    CoefficientBassPositiveActualRightRoute.finish P d s := (routeHomotopy P d).apply_one s

theorem route_bottom (r : I) : route P d (r, 0) =
    CoefficientBassPositiveActualRightRoute.minusTip P d := by
  change ((middle P d).trans (first P d)) (r, 0) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P (firstArrow d) (secondArrow d)).source _
  · exact (firstComparison P (firstArrow d) (secondArrow d)).source _

theorem route_top (r : I) : route P d (r, 1) =
    CoefficientBassPositiveActualRightRoute.plusTip P d := by
  change ((middle P d).trans (first P d)) (r, 1) = _
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (middleComparison P (firstArrow d) (secondArrow d)).target _
  · exact (firstComparison P (firstArrow d) (secondArrow d)).target _

end Quillen.PerfectComplexes.CoefficientBassPositiveActualLeftRoute
