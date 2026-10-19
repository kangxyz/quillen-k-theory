/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityNodes

/-! Full dependent-node and native-surface regressions for the global identity input rectangles. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalRawBassInputIdentityNodes
open InputIdentityNodes BassH0Merge
variable (X : Scheme.{u})

/-- The whole positive first unit row occurs in the actual thirty-one-node input diagram. -/
theorem positive_first_unit_row (i : Fin 3) :
    nodes X (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
      chartSideNodes X plus plus_projection (![0, 1, 2] i) :=
  (plus_nodes X _).trans (chart_unit_right X plus plus_projection i)

/-- The whole inverse middle unit row retains its separate maps and original anchors. -/
theorem inverse_middle_unit_row (i : Fin 3) :
    nodes X (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
      chartSideNodes X minus minus_projection (![0, 4, 5] i) :=
  (minus_nodes X _).trans (chart_unit_left X minus minus_projection i)

/-- The original degree-zero cylinder retains both full times under the identity reference. -/
theorem native_zero_original (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space 0) :
    prespectrumSimplexFamily (simplex X) 0 (BassH0Diagram.parameter (r, s), x) =
      (inputDescPasting (𝟙 X)).toSquare.level 0 (r, (s, x)) :=
  (cylinder_native X 0 r s x).trans (inputComparisonHomotopy_cylinder (𝟙 X) 0 r s x)

end QuillenTest.GlobalRawBassInputIdentityNodes
