/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBottomSupport

/-! The literal bottom parameter is covered by supports that preserve the concrete whole order. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.CoefficientBassUnitBottomSupport
open Quillen.PerfectComplexes.CoefficientBassUnitBottomSupport
open Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder

theorem exact_ordered_bottom_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 8) (w : StdSimplex ℝ (Fin 4)),
      StrictMono (bottomIndex ∘ (face i).toOrderHom) ∧
      StdSimplex.map (bottomIndex ∘ (face i).toOrderHom) w =
        StdSimplex.map bottomIndex
          (Quillen.PerfectComplexes.CoefficientBassUnitBottom.parameter.{u} z) := by
  obtain ⟨i, w, hw⟩ := bottom_support.{u} z
  refine ⟨i, w, bottom_grid_support i, ?_⟩
  rw [StdSimplex.map_comp, hw]

end QuillenTest.CoefficientBassUnitBottomSupport
