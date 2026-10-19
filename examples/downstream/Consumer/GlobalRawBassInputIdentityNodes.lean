/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityNodes

/-! An independent client of both complete identity-unit rows in the original input diagram. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Consumer.GlobalRawBassInputIdentityNodes
open InputIdentityNodes BassH0Merge

/-- The two different original charts expose their actual full unit rows in one input family. -/
theorem both_original_unit_rows (X : Scheme.{u}) (i : Fin 3) :
    nodes X (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
        chartSideNodes X plus plus_projection (![0, 1, 2] i) ∧
    nodes X (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
        chartSideNodes X minus minus_projection (![0, 4, 5] i) :=
  ⟨(plus_nodes X _).trans (chart_unit_right X plus plus_projection i),
    (minus_nodes X _).trans (chart_unit_left X minus minus_projection i)⟩

end Consumer.GlobalRawBassInputIdentityNodes
