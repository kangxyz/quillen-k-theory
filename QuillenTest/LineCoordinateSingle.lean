/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.TensorToUnit

/-! Exact original single-map recovery through the actual unit comparison. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace QuillenTest.LineCoordinateSingle

/-- The actual comparison recovers the original single of f in every chosen degree. -/
theorem original_single_arrow {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeftSingleUnitIso X L n).inv ≫
        (AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit f).app
          ((CochainComplex.singleFunctor X.Modules n).obj
            (SheafOfModules.unit X.ringCatSheaf)) =
      (CochainComplex.singleFunctor X.Modules n).map f := by
  rw [AlgebraicGeometry.Scheme.Modules.Complex.tensorToUnit_single]
  simp

end QuillenTest.LineCoordinateSingle
