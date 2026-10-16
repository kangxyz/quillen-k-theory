/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic

/-!
# The original structure unit is finite locally free

The actual one-generator free-module comparison supplies the existing structure-sheaf unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
lemma unit_finiteLocallyFree (X : Scheme.{u}) :
    IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  exact finiteLocallyFree_of_iso e


end Quillen.PerfectComplexes.ProjectiveLine.Euler
end
end
