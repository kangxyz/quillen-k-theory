/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.QuasiCompactCategory
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! The unchanged original compact affine base, independent of the flasque Phi comparison. -/
@[expose] public section
noncomputable section
open AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands

/-- The same original compact affine base used by nativeTwoSummands. -/
abbrev affineBase (R : CommRingCat.{u}) : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u} :=
  ⟨Spec R, inferInstance⟩

end Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
