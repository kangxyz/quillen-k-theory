/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPasting

/-! The two endpoint height paths are fixed throughout the original three-square paste. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)

/-- The full source height path remains fixed, with the original cap word endpoint. -/
theorem family_source (r h : I) : family P α f negative ![r, 0, h] =
    leftWord P α f negative 0 h := by
  exact congrArg (fun g ↦ g h)
    (((pasted P α f negative).source r).trans (leftWord P α f negative).source.symm)

/-- The full target height path remains fixed, with the original cap word endpoint. -/
theorem family_target (r h : I) : family P α f negative ![r, 1, h] =
    leftWord P α f negative 1 h := by
  exact congrArg (fun g ↦ g h)
    (((pasted P α f negative).target r).trans (leftWord P α f negative).target.symm)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
