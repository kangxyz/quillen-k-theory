/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassRectangleSpecialization

/-! Exact scalar path endpoints of the coefficient composition comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

def outerSquarePath := targetTotal.symm.trans sourceTotal

def originalComparisonSource :=
  ((firstRestriction.symm.trans secondRestriction).trans
    (middleChart.symm.trans lastRestriction)).symm

def originalComparisonTarget :=
  (targetChart.symm.trans outerSquarePath).trans sourceChart

/-- Reverse the rectangle using exactly the original path-time reversal, then transport only
its endpoint path type along literal `Path.trans_symm` equalities. -/
def originalComparisonParameter :
    originalComparisonSource.Homotopy originalComparisonTarget :=
  rectangleParameter.symm₂.cast rfl (by
    simp only [Path.trans_symm, Path.symm_symm]
    rfl)
end Quillen.PerfectComplexes.DoubleSquareScalarPaths

namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The scalar comparison has the precise constituent endpoint path needed for the chart word. -/
theorem comparisonParameter_nativeLift :
    HomotopyLift (simplex P α u v)
      DoubleSquareScalarPaths.originalComparisonParameter
      (CoefficientTransformationComposition.comparison P α u v) := by
  intro n r s x
  exact comparison_nativeLift P α u v n r s x

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
