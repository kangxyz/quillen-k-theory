/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.BassScalarBoundaryLiftOps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBoundaryTracks

/-! The exact coefficient moving-square boundary has one common-simplex scalar parameter. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

/-- The original coefficient boundary word with its actual total, chart, and direct-square paths. -/
def coefficientBoundaryParameter :=
  Path.Homotopy.boundaryOfComparison originalComparisonParameter
end Quillen.PerfectComplexes.DoubleSquareScalarPaths

namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The literal native moving-square boundary is evaluated from one scalar simplex surface. -/
theorem boundary_nativeLift :
    HomotopyLift (simplex P α u v)
      DoubleSquareScalarPaths.coefficientBoundaryParameter
      (CoefficientTransformationComposition.boundary P α u v) := by
  let S := simplex P α u v
  have h := HomotopyLift.boundaryOfComparison S
    (targetComposition_path P α u v)
    (outerSquare_path P α u v)
    (sourceComposition_path P α u v)
    (comparisonParameter_nativeLift P α u v)
  exact h

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
