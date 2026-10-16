/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitSupportOrder

/-! Every primitive support of both complete original Laurent unit squares preserves the
concrete 48-node order, although neither complete eight-vertex order must be monotone. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
namespace QuillenTest.OriginalUnitSquareSupport
open Quillen.PerfectComplexes.OriginalUnitSquareSupport
open Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder

theorem actual_triangle_labels (i : Fin 6) (j : Fin 3) :
    (face i).toOrderHom j = unitTriangle i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem positive_whole_square_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 6) (w : StdSimplex ℝ (Fin 3)),
      StdSimplex.map (plusSideIndex ∘ (face i).toOrderHom) w =
        StdSimplex.map plusSideIndex
          (Quillen.PerfectComplexes.OriginalUnitSquareSimplex.squareParameter z) := by
  obtain ⟨i, w, hw⟩ := square_support z
  refine ⟨i, w, ?_⟩
  rw [StdSimplex.map_comp, hw]

theorem positive_actual_support_order (i : Fin 6) :
    StrictMono (plusSideIndex ∘ (face i).toOrderHom) := by
  intro j k hjk
  simpa only [Function.comp_apply, actual_triangle_labels] using plus_side_support i hjk

theorem inverse_actual_support_order (i : Fin 6) :
    StrictMono (minusSideIndex ∘ (face i).toOrderHom) := by
  intro j k hjk
  simpa only [Function.comp_apply, actual_triangle_labels] using minus_side_support i hjk

end QuillenTest.OriginalUnitSquareSupport
