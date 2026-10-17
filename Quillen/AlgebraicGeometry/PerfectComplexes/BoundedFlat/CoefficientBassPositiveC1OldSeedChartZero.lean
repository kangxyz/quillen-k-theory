/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ChartSharedNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundarySeam

/-! Five full reference-node joins for the original chart-zero and positive-movement words. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1OldSeedChartZero
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Five indices of the original chart's reversed-target-total then source-total word. -/
def chartZeroIndex : Fin 5 → Fin 18 := ![0, 14, 15, 1, 2]

/-- Five indices of the original positive movement in its complete H0 rectangle. -/
def movementIndex : Fin 5 → Fin 18 := ![9, 10, 11, 12, 13]

/-- The entire Laurent half retains all three actual chart and H0 reference isomorphisms. -/
theorem laurent_row (i : Fin 3) :
    CoefficientBassPositiveC1BoundaryLift.chartNodes P p q
      (BassH0Merge.outerIndex i) =
    BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (BassH0Merge.rightIndex i))) :=
  ((BassH0Merge.plus_laurent_rows P p q i).trans
    (BassH0Merge.old_plus_node P p q (BassH0Merge.outerIndex i))).symm

/-- The entire polynomial half retains all three actual chart and H0 reference isomorphisms. -/
theorem polynomial_row (i : Fin 3) :
    CoefficientBassPositiveC1BoundaryLift.chartNodes P p q
      (BassH0Merge.initialIndex i) =
    BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (BassH0Merge.rightIndex i))) :=
  ((BassH0Merge.plus_polynomial_rows P p q i).trans
    (BassH0Merge.old_plus_node P p q (BassH0Merge.initialIndex i))).symm

/-- All five full dependent nodes agree in the original common reference, before evaluation. -/
theorem full_nodes (i : Fin 5) :
    CoefficientBassPositiveC1BoundaryLift.chartNodes P p q (chartZeroIndex i) =
      BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom (movementIndex i)) := by
  fin_cases i
  · exact laurent_row P p q 0
  · exact laurent_row P p q 1
  · exact laurent_row P p q 2
  · exact polynomial_row P p q 1
  · exact polynomial_row P p q 2

end Quillen.PerfectComplexes.CoefficientBassPositiveC1OldSeedChartZero
