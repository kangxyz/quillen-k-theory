/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeAffineBase

/-! Moving the original affine abbreviation retains its literal scheme and compact witness. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open AlgebraicGeometry
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueTwoSummands
universe u
namespace QuillenTest.NativeAffineBase

/-- The original fully qualified abbreviation remains the same compact affine object. -/
theorem affine_base_is_original (R : CommRingCat.{u}) :
    affineBase R = (⟨Spec R, inferInstance⟩ : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u})
      := rfl

/-- Its original underlying scheme is still literally Spec R. -/
theorem affine_base_original_scheme (R : CommRingCat.{u}) :
    (affineBase R).obj = Spec R := rfl

end QuillenTest.NativeAffineBase
