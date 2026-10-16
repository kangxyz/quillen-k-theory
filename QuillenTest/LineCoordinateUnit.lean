/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit

/-! Exact original-arrow cancellation at the original unit coefficient. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing
namespace QuillenTest.LineCoordinateUnit

/-- Cancelling the original right-unit comparison recovers exactly the supplied arrow. -/
theorem original_arrow_from_unit_coordinate {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (tensorRightUnitIso X.sheaf).inv.app L ≫
        (AlgebraicGeometry.Scheme.Modules.tensorToUnit f).app (SheafOfModules.unit X.ringCatSheaf)
          = f := by
  rw [AlgebraicGeometry.Scheme.Modules.tensorToUnit_unit]
  simp

end QuillenTest.LineCoordinateUnit
