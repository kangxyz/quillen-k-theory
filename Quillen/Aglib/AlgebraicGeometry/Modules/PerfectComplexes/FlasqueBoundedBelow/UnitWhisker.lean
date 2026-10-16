/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic

/-!
# Whiskering the original Godement augmentation

Every actual functor into lower-bounded perfect complexes retains the same pointwise totalization unit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
open AlgebraicGeometry.Scheme.Modules.Godement
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
/-- The actual forward line augmentation before right tensor. -/
def totalUnitWhisker {C : Type (u + 1)} [Category.{u} C] (Y : Scheme.{u})
    (F : C ⥤ BoundedBelow.Obj Y) :
    F ⟶ (F ⋙ FlasqueBoundedBelow.total Y) ⋙ FlasqueBoundedBelow.inclusion Y :=
  Functor.whiskerLeft F (FlasqueBoundedBelow.unit Y)

/-- The component is the same original total augmentation, with no replacement chain map. -/
lemma totalUnitWhisker_app {C : Type (u + 1)} [Category.{u} C] (Y : Scheme.{u})
    (F : C ⥤ BoundedBelow.Obj Y) (K : C) :
    (totalUnitWhisker Y F).app K = (FlasqueBoundedBelow.unit Y).app (F.obj K) := rfl


end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
end
end
