/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBoundarySpecialization

/-! Exact scalar moving square and native terminal chart pause, with quotient collapse. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

/-- Explicit common-simplex parameter after native `ThreeSideSquare` collapse. -/
def coefficientMovingSquareParameter :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  collapsed coefficientBoundaryParameter

/-- Explicit common-simplex parameter with the original terminal chart pause and collapse. -/
def coefficientPausedSquareParameter :
    C(unitInterval × unitInterval, StdSimplex ℝ (Fin 18)) :=
  collapsed (pauseRightParameter coefficientBoundaryParameter)
end Quillen.PerfectComplexes.DoubleSquareScalarPaths

namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original moving square, not just its four edges, is the scalar collapsed surface. -/
theorem movingSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (simplex P α u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s), x) =
      (CoefficientTransformationComposition.movingSquare P α u v).level n
        (r, (s, x)) :=
  HomotopyLift.toSquare _ (boundary_nativeLift P α u v) n r s x

/-- The actual native `pauseRight` chart square keeps its whole scalar parameter and collapse. -/
theorem pausedSquare_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, M.obj a)))).space n) :
    prespectrumSimplexFamily (simplex P α u v) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
      ((CoefficientTransformationComposition.movingSquare P α u v).pauseRight).level n
        (r, (s, x)) :=
  HomotopyLift.pauseRight_square _ (boundary_nativeLift P α u v)
    (targetComposition_path P α u v)
    (compositeSquare_path P α u v)
    (sourceComposition_path P α u v) n r s x

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
