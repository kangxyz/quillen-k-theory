/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MiddleCylinderProduct
public import Quillen.Topology.Prespectrum.NativeMovingSquareCells

/-! Exact all-parameter cells of the original M vertex-composition stage. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMComponents
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- This abbreviation is precisely the prescribed native M face, without changing any data. -/
abbrev originalM := (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
  (boundedFlatCoefficientBassSquareComparison P c)

/-- Native moving-square descent retains both original times on every cylinder generator. -/
theorem vertex_cylinder (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) =
    (boundedFlatCoefficientPolynomialSpanCompositionSquare P u v).level n (r, (t, x)) := rfl

/-- The first cylinder half is the actual moving polynomial square on the original plus chart. -/
theorem vertex_plus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (lower t, x))) =
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n
      ((boundedFlatCoefficientPolynomialCompositionSquare P u v).level n (r, (t, x))) := by
  rw [vertex_cylinder]
  unfold boundedFlatCoefficientPolynomialSpanCompositionSquare
  rw [HomotopyPushout.identicalMoving_lower]
  rfl

/-- The original middle quarter keeps the two independently moving native inputs. -/
theorem vertex_middle_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x))) =
    (boundedFlatCoefficientBassSquareComparison P c).map n
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)) n
        (t, (boundedFlatCoefficientCompositionHomotopy P u v).level n (r, x))) := by
  rw [vertex_cylinder]
  unfold boundedFlatCoefficientPolynomialSpanCompositionSquare
  rw [HomotopyPushout.identicalMoving_middle]

/-- The final quarter retains the original reversed square on the separate inverse chart. -/
theorem vertex_minus_value (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (upper t), x))) =
    (boundedFlatPerfectPrespectrumMap (laurentMinus P c)).map n
      ((boundedFlatCoefficientPolynomialCompositionSquare P u v).level n
        (r, (unitInterval.symm t, x))) := by
  rw [vertex_cylinder]
  unfold boundedFlatCoefficientPolynomialSpanCompositionSquare
  rw [HomotopyPushout.identicalMoving_upper]
  rfl

/-- The first original composition half is exactly the vertex stage, at its native speed. -/
theorem originalM_lower (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (originalM P u v).level n
      (lower r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) =
    (boundedFlatCoefficientBassSquareComparison P c).map n
      ((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) := by
  change (boundedFlatCoefficientBassSquareComparison P c).map n
    (((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).trans
      (boundedFlatCoefficientPolynomialSpanReparameterization P u v).symm).level n
      (lower r, _)) = _
  rw [Homotopy.trans_lower_cell]

/-- Every positive first-stage M parameter has this exact original common-simplex evaluation. -/
theorem plus_cell_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (plusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, t), x) =
    (originalM P u v).level n
      (lower r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (lower t, x)) :=
  (plus_native P u v n r t x).trans
    ((vertex_plus_value P u v n r t x).symm.trans (originalM_lower P u v n r (lower t) x).symm)

/-- Every middle first-stage parameter retains the real independently varying product evaluation. -/
theorem middle_cell_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P u v) n (middleParameter.{u} (r, t), x) =
    (originalM P u v).level n
      (lower r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) :=
  (middle_native P u v n r t x).trans ((vertex_middle_value P u v n r t x).symm.trans
    (originalM_lower P u v n r (upper (lower t)) x).symm)

/-- The complete inverse first-stage cell retains the actual native path reversal. -/
theorem minus_cell_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (minusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm t), x) =
    (originalM P u v).level n
      (lower r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (upper t), x)) :=
  (minus_native P u v n r t x).trans ((vertex_minus_value P u v n r t x).symm.trans
    (originalM_lower P u v n r (upper (upper t)) x).symm)

end Quillen.PerfectComplexes.BassMComponents
