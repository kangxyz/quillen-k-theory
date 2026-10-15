/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassScalarComparison

/-! Exact four constituent route tracks of the original coefficient rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {M N : Under R ⥤ Under R} (α : M ⟶ N)
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
open DoubleSquareScalarPaths

/-- The target coefficient composition retains its exact original time. -/
theorem targetComposition_path :
    PathLift (simplex P α u v) targetChart
      (CoefficientTransformationComposition.targetComposition P α u v) := by
  let S := simplex P α u v
  change PathLift S targetChart
    (CoefficientTransformationComposition.targetComposition P α u v)
  have h := HomotopyLift.target S (comparisonParameter_nativeLift P α u v)
  have h' := PathLift.trans_left S h
  intro n t x
  have hv := (PathLift.trans_left S h') n (unitInterval.symm t) x
  change prespectrumSimplexFamily S n
      (targetChart (unitInterval.symm (unitInterval.symm t)), x) =
    (CoefficientTransformationComposition.targetComposition P α u v).level n
      (unitInterval.symm (unitInterval.symm t), x) at hv
  rw [unitInterval.symm_symm] at hv
  exact hv

/-- The original source composition retains its exact original time. -/
theorem sourceComposition_path :
    PathLift (simplex P α u v) sourceChart
      (CoefficientTransformationComposition.sourceComposition P α u v) := by
  let S := simplex P α u v
  have h := HomotopyLift.target S (comparisonParameter_nativeLift P α u v)
  exact PathLift.trans_right S h

/-- The direct outer coefficient square retains its exact original time. -/
theorem outerSquare_path :
    PathLift (simplex P α u v) outerSquarePath
      (CoefficientTransformationComposition.square P α (u ≫ v)) := by
  let S := simplex P α u v
  have h := HomotopyLift.target S (comparisonParameter_nativeLift P α u v)
  exact PathLift.trans_right S (PathLift.trans_left S h)

/-- Both successive coefficient squares are one exact scalar route. -/
theorem compositeSquare_path :
    PathLift (simplex P α u v) originalComparisonSource
      (CoefficientTransformationComposition.compositeSquare P α u v) :=
  HomotopyLift.source _ (comparisonParameter_nativeLift P α u v)

end Quillen.PerfectComplexes.CoefficientTransformationComposition.Scalar
