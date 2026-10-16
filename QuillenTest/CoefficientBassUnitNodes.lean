/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNodes

/-! Public consumers of the original reference-node and primitive-face assembly.
These compare actual original diagrams, including the two different Laurent charts. -/

@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CoefficientBassUnitNodes CoefficientBassUnitSupportOrder
universe u

namespace QuillenTest.CoefficientBassUnitNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive polynomial piece remains the actual postcomposed original unit simplex. -/
theorem original_positive_top_piece :
    ((simplex P a).face topFace).face CoefficientPolynomialSpanUnitTop.plusFace =
      CoefficientPolynomialSpanUnitSimplex.plusSimplex P a := by
  rw [top_face, CoefficientPolynomialSpanUnitTop.plus_face]

/-- The inverse polynomial piece independently keeps the inverse-chart postmap. -/
theorem original_negative_top_piece :
    ((simplex P a).face topFace).face CoefficientPolynomialSpanUnitTop.minusFace =
      CoefficientPolynomialSpanUnitSimplex.minusSimplex P a := by
  rw [top_face, CoefficientPolynomialSpanUnitTop.minus_face]

/-- The complete top middle remains the literal identity by projection product diagram. -/
theorem original_top_middle :
    ((simplex P a).face topFace).face CoefficientPolynomialSpanUnitTop.middleFace =
      CoefficientPolynomialSpanUnitSimplex.middleSimplex P a := by
  rw [top_face, CoefficientPolynomialSpanUnitTop.middle_face]

/-- H0 and the positive raw Laurent side use the same complete dependent intermediate node. -/
theorem positive_h0_side_intermediate :
    nodes P a (h0Index 10) =
      CoefficientBassUnitBoundaryNodes.plusSideNodes P a 1 := by
  rw [h0_nodes]
  exact CoefficientBassUnitHZeroNodes.h0_plus_side P a 1

/-- The inverse raw source-projection node is retained in the common bottom family. -/
theorem negative_h0_bottom_intermediate :
    nodes P a (h0Index 14) =
      CoefficientBassUnitBoundaryNodes.bottomNodes P a 9 := by
  rw [h0_nodes]
  exact CoefficientBassUnitHZeroNodes.h0_minus_source P a 1

/-- The terminal positive corner is a genuine common-reference node on both faces. -/
theorem positive_bottom_top_corner :
    nodes P a (bottomIndex 8) =
      CoefficientPolynomialSpanUnitNodes.middleNodes P a 12 := by
  rw [bottom_nodes]
  exact CoefficientBassUnitBoundaryNodes.terminal_nodes P a 2

end QuillenTest.CoefficientBassUnitNodes
