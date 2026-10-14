/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexMerged

/-! One pure continuous family for the entire original first M stage. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity Quillen.NativePathCells Quillen.SimplexParameters Quillen.ScalarRectangle
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMVertexOrder

/-- The positive cell retains every scalar point of the original moving square. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map plusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter z), by fun_prop⟩

/-- The original middle product retains both independent parameters. -/
def centerParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map middleIndex (BassMComponents.middleParameter.{u} z), by fun_prop⟩

/-- The inverse cell retains the original reversal of its second scalar coordinate. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (z.1, unitInterval.symm z.2)),
    by fun_prop⟩

/-- The full positive scalar seam follows from its actual shared binary face. -/
theorem plus_center_join (r : unitInterval) :
    plusParameter (r, 1) = centerParameter.{u} (r, 0) := by
  change StdSimplex.map plusIndex _ = StdSimplex.map middleIndex _
  rw [← BassMJoin.moving_source_parameter, ← BassMJoin.middle_plus_parameter,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  apply congrArg (fun f : Fin 3 → Fin 45 ↦ StdSimplex.map f (binaryPath (k := 2) 0 1 2 r))
  funext i
  fin_cases i <;> rfl

/-- The full inverse scalar seam retains the genuine reversed chart boundary. -/
theorem center_minus_join (r : unitInterval) :
    centerParameter.{u} (r, 1) = minusParameter (r, 0) := by
  change StdSimplex.map middleIndex _ = StdSimplex.map minusIndex
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm 0))
  rw [unitInterval.symm_zero, ← BassMJoin.moving_source_parameter,
    ← BassMJoin.middle_minus_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  apply congrArg (fun f : Fin 3 → Fin 45 ↦ StdSimplex.map f (binaryPath (k := 2) 0 1 2 r))
  funext i
  fin_cases i <;> rfl

/-- The two original final cylinder pieces join along their entire proved scalar seam. -/
def tailParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  concatSecond centerParameter.{u} minusParameter center_minus_join

theorem tail_zero (r : unitInterval) : tailParameter.{u} (r, 0) = centerParameter.{u} (r, 0) :=
  concatSecond_zero _ _ _ r

theorem plus_tail_join (r : unitInterval) : plusParameter (r, 1) = tailParameter.{u} (r, 0) :=
  (plus_center_join r).trans (tail_zero r).symm

/-- The first-stage parameter uses the native half, quarter, and quarter cylinder speeds. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  concatSecond plusParameter tailParameter.{u} plus_tail_join

theorem parameter_plus (r t : unitInterval) :
    parameter.{u} (r, lower t) = plusParameter (r, t) :=
  concatSecond_lower _ _ _ r t

theorem parameter_middle (r t : unitInterval) :
    parameter.{u} (r, upper (lower t)) = centerParameter.{u} (r, t) :=
  (concatSecond_upper _ _ _ r (lower t)).trans (concatSecond_lower _ _ _ r t)

theorem parameter_minus (r t : unitInterval) :
    parameter.{u} (r, upper (upper t)) = minusParameter (r, t) :=
  (concatSecond_upper _ _ _ r (upper t)).trans (concatSecond_upper _ _ _ r t)

theorem parameter_zero (r : unitInterval) : parameter.{u} (r, 0) = plusParameter (r, 0) :=
  concatSecond_zero _ _ _ r

theorem parameter_one (r : unitInterval) : parameter.{u} (r, 1) = minusParameter (r, 1) :=
  (concatSecond_one _ _ _ r).trans (concatSecond_one _ _ _ r)

end Quillen.PerfectComplexes.BassMVertexOrder
