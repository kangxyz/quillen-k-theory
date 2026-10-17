/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1OldSeedChartZero
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0Rectangles

/-! Whole chart-zero rail from two ordered binary faces, with the original reversal and clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity Simplicial
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldChartClockedRail
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original first binary row is ordered, separately from the five-node word. -/
def firstFace : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![0, 14, 15], by decide⟩
/-- The original second binary row is separately ordered. -/
def secondFace : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2], by decide⟩
/-- First original movement row inside the positive rectangle. -/
def firstMovementFace : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![9, 10, 11], by decide⟩
/-- Second original movement row inside the positive rectangle. -/
def secondMovementFace : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![9, 12, 13], by decide⟩

/-- Whole first binary path equality retains all three full references. -/
theorem first_binary (s : I) :
    parameter (laurentReference P p q) (chartNodes P p q)
      (binaryPath (k := 17) 0 14 15 s) =
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (binaryPath (BassH0Diagram.plusFace.toOrderHom 9)
        (BassH0Diagram.plusFace.toOrderHom 10) (BassH0Diagram.plusFace.toOrderHom 11) s) := by
  change parameter (laurentReference P p q) (chartNodes P p q)
    (binaryPath (firstFace.toOrderHom 0) (firstFace.toOrderHom 1)
      (firstFace.toOrderHom 2) s) =
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (binaryPath ((firstMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 0)
        ((firstMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 1)
        ((firstMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 2) s)
  rw [← map_binaryPath firstFace 0 1 2 s,
    ← map_binaryPath (firstMovementFace ≫ BassH0Diagram.plusFace) 0 1 2 s]
  change parameter _ _ (StdSimplex.map firstFace.toOrderHom _) =
    parameter _ _ (StdSimplex.map (firstMovementFace ≫ BassH0Diagram.plusFace).toOrderHom _)
  rw [parameter_face, parameter_face]
  apply congrArg (fun N ↦ parameter (laurentReference P p q) N
    (binaryPath (k := 2) 0 1 2 s))
  funext i
  fin_cases i
  · exact CoefficientBassPositiveC1OldSeedChartZero.laurent_row P p q 0
  · exact CoefficientBassPositiveC1OldSeedChartZero.laurent_row P p q 1
  · exact CoefficientBassPositiveC1OldSeedChartZero.laurent_row P p q 2

/-- Whole second binary path equality retains its separate normalization references. -/
theorem second_binary (s : I) :
    parameter (laurentReference P p q) (chartNodes P p q)
      (binaryPath (k := 17) 0 1 2 s) =
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (binaryPath (BassH0Diagram.plusFace.toOrderHom 9)
        (BassH0Diagram.plusFace.toOrderHom 12) (BassH0Diagram.plusFace.toOrderHom 13) s) := by
  change parameter (laurentReference P p q) (chartNodes P p q)
    (binaryPath (secondFace.toOrderHom 0) (secondFace.toOrderHom 1)
      (secondFace.toOrderHom 2) s) =
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (binaryPath ((secondMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 0)
        ((secondMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 1)
        ((secondMovementFace ≫ BassH0Diagram.plusFace).toOrderHom 2) s)
  rw [← map_binaryPath secondFace 0 1 2 s,
    ← map_binaryPath (secondMovementFace ≫ BassH0Diagram.plusFace) 0 1 2 s]
  change parameter _ _ (StdSimplex.map secondFace.toOrderHom _) =
    parameter _ _ (StdSimplex.map (secondMovementFace ≫ BassH0Diagram.plusFace).toOrderHom _)
  rw [parameter_face, parameter_face]
  apply congrArg (fun N ↦ parameter (laurentReference P p q) N
    (binaryPath (k := 2) 0 1 2 s))
  funext i
  fin_cases i
  · exact CoefficientBassPositiveC1OldSeedChartZero.polynomial_row P p q 0
  · exact CoefficientBassPositiveC1OldSeedChartZero.polynomial_row P p q 1
  · exact CoefficientBassPositiveC1OldSeedChartZero.polynomial_row P p q 2

/-- The original paused square starts on the unchanged entire outer word. -/
theorem chart_zero_scalar (s : I) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s) =
      DoubleSquareScalarPaths.outerSquarePath s :=
  collapsed_zero_path (pauseRightParameter DoubleSquareScalarPaths.coefficientBoundaryParameter) s

/-- The whole chart-zero path equals the old movement with precisely its original half clocks. -/
theorem chart_zero (s : I) : chartParameter P p q (0, s) =
    parameter (laurentReference P p q) (BassH0Merge.nodes P p q)
      (ProjectionRectangleParameters.L BassH0Diagram.plusFace s) := by
  change parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s)) = _
  rw [chart_zero_scalar]
  change parameter _ _ (((binaryPath (k := 17) 0 14 15).symm.trans
    (binaryPath 0 1 2)) s) = _
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact first_binary P p q _
  · exact second_binary P p q _

variable (d : Under R)
open CoefficientBassPositiveJ0ConeBoundaries CoefficientBassPositiveJ0Rectangles

/-- Inclusion preserves this whole carrier rail, without cancelling a native evaluator. -/
theorem actual_chart_zero (s : I) :
    CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
      (chartParameter P (firstArrow d) (secondArrow d) (0, s)) =
        positiveMovementMinus P d s := by
  rw [chart_zero]; rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldChartClockedRail
