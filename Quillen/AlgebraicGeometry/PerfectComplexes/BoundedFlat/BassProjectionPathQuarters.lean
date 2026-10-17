/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionPath
public import Quillen.Topology.Path.ScalarPathCells

/-!
# The four original oriented cells of the Bass overlap

The first two cells run opposite to the overlap traversal. Their scalar clocks retain the
original outer and inner half splits, including all shared endpoints.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.SimplexParameters Quillen.NativePathCells Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath

/-- The positive normalization edge runs from the quarter point back to the initial endpoint. -/
def plusNormalizationTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ lower (unitInterval.symm (upper t)), by fun_prop⟩

/-- The positive geometric edge runs from the midpoint back to the quarter point. -/
def plusGeometricTime : C(unitInterval, unitInterval) :=
  ⟨fun t ↦ lower (unitInterval.symm (lower t)), by fun_prop⟩

/-- The inverse geometric edge runs from the midpoint to the third quarter point. -/
def minusGeometricTime : C(unitInterval, unitInterval) := upper.comp lower

/-- The inverse normalization edge runs from the third quarter point to the final endpoint. -/
def minusNormalizationTime : C(unitInterval, unitInterval) := upper.comp upper

theorem plusNormalizationTime_val (t : unitInterval) :
    (plusNormalizationTime t : ℝ) = (1 - (t : ℝ)) / 4 := by
  change (1 - ((t : ℝ) + 1) / 2) / 2 = _
  ring

theorem plusGeometricTime_val (t : unitInterval) :
    (plusGeometricTime t : ℝ) = (2 - (t : ℝ)) / 4 := by
  change (1 - (t : ℝ) / 2) / 2 = _
  ring

theorem minusGeometricTime_val (t : unitInterval) :
    (minusGeometricTime t : ℝ) = (2 + (t : ℝ)) / 4 := by
  dsimp [minusGeometricTime, lower, upper]
  ring

theorem minusNormalizationTime_val (t : unitInterval) :
    (minusNormalizationTime t : ℝ) = (3 + (t : ℝ)) / 4 := by
  dsimp [minusNormalizationTime, upper]
  ring

/-- The first traversed quarter is precisely the reversed normalization edge. -/
theorem parameter_plus_normalization (t : unitInterval) :
    parameter (plusNormalizationTime t) = (edge (k := 4) 1 2) t := by
  change ((binaryPath 0 1 2).symm.trans (binaryPath 0 3 4))
    (lower (unitInterval.symm (upper t))) = _
  rw [path_lower]
  change binaryPath (k := 4) 0 1 2 (unitInterval.symm (unitInterval.symm (upper t))) = _
  rw [unitInterval.symm_symm]
  exact path_upper _ _ t

/-- The second traversed quarter is precisely the reversed geometric edge. -/
theorem parameter_plus_geometric (t : unitInterval) :
    parameter (plusGeometricTime t) = (edge (k := 4) 0 1) t := by
  change ((binaryPath 0 1 2).symm.trans (binaryPath 0 3 4))
    (lower (unitInterval.symm (lower t))) = _
  rw [path_lower]
  change binaryPath (k := 4) 0 1 2 (unitInterval.symm (unitInterval.symm (lower t))) = _
  rw [unitInterval.symm_symm]
  exact path_lower _ _ t

/-- The third quarter retains the original inverse geometric edge. -/
theorem parameter_minus_geometric (t : unitInterval) :
    parameter (minusGeometricTime t) = (edge (k := 4) 0 3) t := by
  change ((binaryPath 0 1 2).symm.trans (binaryPath 0 3 4)) (upper (lower t)) = _
  rw [path_upper]
  exact path_lower _ _ t

/-- The fourth quarter retains the original inverse normalization edge. -/
theorem parameter_minus_normalization (t : unitInterval) :
    parameter (minusNormalizationTime t) = (edge (k := 4) 3 4) t := by
  change ((binaryPath 0 1 2).symm.trans (binaryPath 0 3 4)) (upper (upper t)) = _
  rw [path_upper]
  exact path_upper _ _ t

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The first oriented cell recovers the unchanged native overlap on its original quarter. -/
theorem plus_normalization_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (edge (k := 4) 1 2 t, x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n (plusNormalizationTime t, x) := by
  rw [← parameter_plus_normalization]
  exact native P a n (plusNormalizationTime t) x

/-- The second oriented cell recovers the reversed geometric quarter without a new track. -/
theorem plus_geometric_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (edge (k := 4) 0 1 t, x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n (plusGeometricTime t, x) := by
  rw [← parameter_plus_geometric]
  exact native P a n (plusGeometricTime t) x

/-- The third oriented cell keeps the inverse-chart geometric quarter at every level. -/
theorem minus_geometric_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (edge (k := 4) 0 3 t, x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n (minusGeometricTime t, x) := by
  rw [← parameter_minus_geometric]
  exact native P a n (minusGeometricTime t) x

/-- The final oriented cell retains the distinct inverse normalization intermediate. -/
theorem minus_normalization_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P a) n (edge (k := 4) 3 4 t, x) =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n (minusNormalizationTime t, x) := by
  rw [← parameter_minus_normalization]
  exact native P a n (minusNormalizationTime t) x

end Quillen.PerfectComplexes.BassProjectionPath
