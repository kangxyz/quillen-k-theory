/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0LaurentSharedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryRowMatching

/-! All eight remaining full H0/chart node identities from the original actual binary rows. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire original plus polynomial row agrees through the proved full source node. -/
theorem plus_polynomial_rows (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (initialIndex i))) :=
  binary_rows_source_match (plus_middle_row P u v) (old_plus_initial_row P u v)
    (shared_positive_center_node P u v) rfl (polynomial_composite P u v) i

/-- The entire original minus polynomial row agrees through the proved full source node. -/
theorem minus_polynomial_rows (i : Fin 3) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (initialIndex i))) :=
  binary_rows_source_match (minus_middle_row P u v) (old_minus_initial_row P u v)
    (shared_negative_center_node P u v) rfl (polynomial_composite P u v) i

/-- Full original shared node pair H0[12] = old[1], including its anchored reference. -/
theorem shared_positive_polynomial_raw_node : nodes P u v 12 = BassReferenceMerge.nodes P u v 1 :=
  plus_polynomial_rows P u v 1

/-- Full original shared node pair H0[13] = old[2], including its anchored reference. -/
theorem shared_positive_polynomial_target_node :
    nodes P u v 13 = BassReferenceMerge.nodes P u v 2 :=
  plus_polynomial_rows P u v 2

/-- Full original shared node pair H0[23] = old[25], including its anchored reference. -/
theorem shared_negative_polynomial_raw_node : nodes P u v 23 = BassReferenceMerge.nodes P u v 25 :=
  minus_polynomial_rows P u v 1

/-- Full original shared node pair H0[24] = old[26], including its anchored reference. -/
theorem shared_negative_polynomial_target_node :
    nodes P u v 24 = BassReferenceMerge.nodes P u v 26 :=
  minus_polynomial_rows P u v 2

end Quillen.PerfectComplexes.BassH0Merge
