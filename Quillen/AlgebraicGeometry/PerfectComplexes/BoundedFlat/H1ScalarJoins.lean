/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ReindexedParameters

/-! Literal complete scalar seams of the original H1 cells in the actual common coordinates. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH1Join

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Order
open BassH1Join

theorem map_nested_join {p q : ℕ} (f : Fin p → Fin 131) (g : Fin 5 → Fin p)
    (f' : Fin q → Fin 131) (g' : Fin 5 → Fin q) (z : StdSimplex ℝ (Fin 5))
    (h : f ∘ g = f' ∘ g') :
    StdSimplex.map f (StdSimplex.map g z) = StdSimplex.map f' (StdSimplex.map g' z) :=
  (StdSimplex.map_comp z g f).symm.trans
    ((congrArg (fun k ↦ StdSimplex.map k z) h).trans (StdSimplex.map_comp z g' f'))

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_plus_scalar (t : unitInterval) :
    firstParameter (1, lower t) = plusProductParameter.{u} (0, t) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (1, lower t)) =
    StdSimplex.map plusProductIndex (BassH1Components.plusParameter.{u} (0, t))
  rw [← first_plus_parameter, product_plus_column_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_middle_scalar (t : unitInterval) :
    firstParameter (1, upper (lower t)) = middleParameter (0, t) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (1, upper (lower t))) =
    StdSimplex.map middleIndex (BassH0Diagram.parameter (0, t))
  rw [← first_middle_parameter, ← middle_source_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_minus_scalar (t : unitInterval) :
    firstParameter (1, upper (upper t)) = minusProductParameter.{u} (0, t) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (1, upper (upper t))) =
    StdSimplex.map minusProductIndex (BassH1Components.minusParameter.{u} (0, t))
  rw [← first_minus_parameter, product_minus_column_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem plus_middle_scalar (s : unitInterval) :
    plusProductParameter.{u} (s, 1) = middleParameter (s, 0) := by
  change StdSimplex.map plusProductIndex (BassH1Components.plusParameter.{u} (s, 1)) =
    StdSimplex.map middleIndex (BassH0Diagram.parameter (s, 0))
  rw [product_plus_row_parameter, ← middle_plus_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem minus_middle_scalar (s : unitInterval) :
    minusProductParameter.{u} (s, 0) = middleParameter (s, 1) := by
  change StdSimplex.map minusProductIndex (BassH1Components.minusParameter.{u} (s, 0)) =
    StdSimplex.map middleIndex (BassH0Diagram.parameter (s, 1))
  rw [product_minus_row_parameter, ← middle_minus_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_bottom_scalar (t : unitInterval) :
    firstParameter (0, t) = bottomParameter.{u} (1, t) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (0, t)) =
    StdSimplex.map oldIndex (BassSupportOrder.bottomParameter.{u} (1, t))
  rw [← middle_source_parameter, ← old_bottom_edge_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_old_plus_scalar (s : unitInterval) :
    firstParameter (s, 0) = plusParameter (1, lower s) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (s, 0)) =
    StdSimplex.map oldIndex (BassSupportOrder.plusParameter (1, lower s))
  rw [← middle_plus_parameter, ← old62_plus_first_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem first_old_minus_scalar (s : unitInterval) :
    firstParameter (s, 1) = minusParameter (1, lower s) := by
  change StdSimplex.map firstIndex (BassH0Diagram.parameter (s, 1)) =
    StdSimplex.map oldIndex (BassSupportOrder.minusParameter (1, lower s))
  rw [← middle_minus_parameter, ← old62_minus_first_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem product_old_plus_scalar (s : unitInterval) :
    plusProductParameter.{u} (s, 0) = plusParameter (1, upper s) := by
  change StdSimplex.map plusProductIndex (BassH1Components.plusParameter.{u} (s, 0)) =
    StdSimplex.map oldIndex (BassSupportOrder.plusParameter (1, upper s))
  rw [product_plus_outer_parameter, ← old62_plus_second_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

/-- The complete original seam retains its literal scalar values and original time coordinates. -/
theorem product_old_minus_scalar (s : unitInterval) :
    minusProductParameter.{u} (s, 1) = minusParameter (1, upper s) := by
  change StdSimplex.map minusProductIndex (BassH1Components.minusParameter.{u} (s, 1)) =
    StdSimplex.map oldIndex (BassSupportOrder.minusParameter (1, upper s))
  rw [product_minus_outer_parameter, ← old62_minus_second_parameter]
  apply map_nested_join
  funext i
  fin_cases i <;> rfl

end Quillen.PerfectComplexes.BassH1Order
