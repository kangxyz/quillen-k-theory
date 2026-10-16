/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitSupportOrder

/-! Public consumers of the finite unit-cube support certificate. In particular, the certificate
must not be confused with an order-preserving embedding of an entire bottom or side simplex. -/

@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder

namespace QuillenTest.CoefficientBassUnitSupportOrder

theorem bottom_primitive_monotone (i : Fin 8) : Monotone (bottomIndex ∘ bottomGridFace i) :=
  (bottom_grid_support i).monotone

theorem side_primitive_monotone (i : Fin 6) : Monotone (plusSideIndex ∘ unitTriangle i) :=
  (plus_side_support i).monotone

/-- The actual finite certificate deliberately does not order the unused full bottom simplex. -/
theorem bottom_whole_not_monotone : ¬ Monotone bottomIndex := by decide

/-- Only primitive unit triangles, rather than the entire side simplex, can be transferred. -/
theorem side_whole_not_monotone : ¬ Monotone plusSideIndex := by decide

/-- Both Laurent endpoints agree across the top, side and bottom labels. -/
theorem both_terminal_labels :
    topIndex 22 = bottomIndex 8 ∧ topIndex 24 = bottomIndex 14 := by decide

/-- H0's positive source endpoint reaches the same label through two independently indexed faces. -/
theorem positive_source_corner : h0Index (h0PlusIndex 11) = plusSideIndex 2 ∧
    h0Index (h0PlusIndex 11) = bottomIndex 6 := by decide

end QuillenTest.CoefficientBassUnitSupportOrder
