/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitStableOperation
public import QuillenTest.ExactSelfTrackStableOperation

/-! # Literal inverse-unit stable operation consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.GlobalUnitStableOperation

/-- Original flat pullback and the literal inverse unit are retained in negative degree. -/
theorem inverse_unit_negative_one {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) :
    (perfectFlatUnitHomotopy f q⁻¹).stableOperation (-1) =
      -(perfectFlatUnitHomotopy f q).stableOperation (-1) :=
  perfectFlatUnitHomotopy_stableOperation_inv f q (-1)

/-- The same original zero-degree operation has the inverse sign. -/
theorem inverse_unit_zero {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) :
    (perfectFlatUnitHomotopy f q⁻¹).stableOperation 0 =
      -(perfectFlatUnitHomotopy f q).stableOperation 0 :=
  perfectFlatUnitHomotopy_stableOperation_inv f q 0

end QuillenTest.GlobalUnitStableOperation
