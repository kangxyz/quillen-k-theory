/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1EightEdges

/-! The unchanged original polynomial composition diagram and its native boundary tracks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMComponents
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

abbrev polynomialSource := NormalizedTripleSimplex.sourceMap
  (polynomialProjection P c) (coefficientMap P v) (coefficientMap P u)

abbrev polynomialNodes := DoubleSquareMergedSimplex.nodes
  (coefficientMap P u) (coefficientMap P v)
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm

def polynomialSimplex := ModelSimplex.ofIsos (polynomialSource P u v)
  (fun i ↦ (polynomialNodes P u v i).1) (fun i ↦ (polynomialNodes P u v i).2)

/-- The entire original polynomial diagram is the actual coefficient-transformation rectangle. -/
theorem polynomial_simplex_original : polynomialSimplex P u v =
    CoefficientTransformationComposition.Scalar.simplex P (polynomialUnderCoefficient R) u v := rfl

/-- The actual native polynomial rectangle is evaluated without changing its original endpoints. -/
theorem polynomial_rectangle_lift : HomotopyLift (polynomialSimplex P u v)
    DoubleSquareScalarPaths.rectangleParameter
    (boundedFlatCoefficientPolynomialTransposedRectangle P u v) :=
  DoubleSquareScalarPaths.original_rectangle_nativeLift
    (coefficientMap P u) (coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (boundedFlatCoefficientPolynomialGeometricNaturality P u).symm
    (boundedFlatCoefficientPolynomialGeometricNaturality P v).symm

/-- The actual ofLevels comparison retains the original reversal and scalar endpoint casts. -/
theorem polynomial_comparison_lift : HomotopyLift
    (polynomialSimplex P u v) DoubleSquareScalarPaths.originalComparisonParameter
    (boundedFlatCoefficientPolynomialSquareCompositionComparison P u v) := by
  intro n r s x
  exact (HomotopyLift.symmPath _ (polynomial_rectangle_lift P u v)) n r s x

/-- The target composition track has its original complete scalar path. -/
theorem polynomial_target_path : PathLift (polynomialSimplex P u v)
    DoubleSquareScalarPaths.targetChart
    (boundedFlatCoefficientPolynomialTargetCompositionTrack P u v) := by
  let S := polynomialSimplex P u v
  have h := HomotopyLift.target S (polynomial_comparison_lift P u v)
  have h' := PathLift.trans_left S h
  intro n t x
  have hv := (PathLift.trans_left S h') n (unitInterval.symm t) x
  change prespectrumSimplexFamily S n
    (DoubleSquareScalarPaths.targetChart (unitInterval.symm (unitInterval.symm t)), x) =
    (boundedFlatCoefficientPolynomialTargetCompositionTrack P u v).level n
      (unitInterval.symm (unitInterval.symm t), x) at hv
  rw [unitInterval.symm_symm] at hv
  exact hv

/-- The source composition track retains its complete original coefficient parameter. -/
theorem polynomial_source_path : PathLift (polynomialSimplex P u v)
    DoubleSquareScalarPaths.sourceChart
    (boundedFlatCoefficientPolynomialSourceCompositionTrack P u v) :=
  PathLift.trans_right _ (HomotopyLift.target _ (polynomial_comparison_lift P u v))

/-- The direct polynomial square retains its entire original scalar path. -/
theorem polynomial_direct_path : PathLift (polynomialSimplex P u v)
    DoubleSquareScalarPaths.outerSquarePath
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v)) :=
  PathLift.trans_right _ (PathLift.trans_left _
    (HomotopyLift.target _ (polynomial_comparison_lift P u v)))

end Quillen.PerfectComplexes.BassMComponents
