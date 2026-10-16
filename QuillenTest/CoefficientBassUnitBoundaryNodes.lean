/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitHZeroNodes

/-! Named consumers of actual shared-reference nodes across independent unit-cube faces.
These test the geometric nodes themselves, rather than only their finite labels or evaluations. -/

@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CoefficientPolynomialSpanUnitNodes CoefficientBassUnitBoundaryNodes
open CoefficientBassUnitHZeroNodes
universe u
namespace QuillenTest.CoefficientBassUnitBoundaryNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive side, top square and terminal product grid have one complete corner node. -/
theorem positive_terminal_corner : plusSideNodes P a 7 = middleNodes P a 12 :=
  (plus_top_target P a).trans (plus_seven P a)

/-- The inverse chart has its separate terminal corner with exactly the same reference. -/
theorem negative_terminal_corner : minusSideNodes P a 7 = middleNodes P a 14 :=
  (minus_top_target P a).trans (minus_seven P a)

/-- The two H0 boundary routes meet the same original positive top-square node. -/
theorem positive_h0_side_top_corner :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom 13) = plusNodes P a 2 :=
  (h0_plus_side P a 4).trans (plus_top_first P a)

/-- The negative raw normalization intermediate is retained across H0 and the bottom family. -/
theorem negative_raw_projection_node :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom 3) = bottomNodes P a 9 :=
  h0_minus_source P a 1

/-- Every original terminal projection node is shared before evaluating either native family. -/
theorem all_terminal_projection_nodes (j : Fin 5) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (j, 2)) =
      middleNodes P a (Quillen.SimplexGrid.index 2 4 (2, j)) :=
  terminal_nodes P a j

end QuillenTest.CoefficientBassUnitBoundaryNodes
