/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict

/-!
# Original strict-perfect inclusion and Godement total

The literal strict inclusion and actual flasque total retain their underlying complexes and each specified strict lower bound.
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
namespace Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
/-- Literal inclusion of the original strict complex into the lower-bounded model. -/
def strictToBoundedBelow (X : Scheme.{u}) : StrictPerfect X ⥤ BoundedBelow.Obj X :=
  ObjectProperty.ιOfLE (fun K hK => by
    obtain ⟨a, b, h⟩ := hK.1
    exact ⟨locallyPerfect_of_strictPerfect hK, a,
      (CochainComplex.isStrictlyGE_iff K a).mpr (fun i hi => h i (Or.inl hi))⟩)

/-- Actual base Godement totalization of the original strict source complex. -/
def strictTotal (X : Scheme.{u}) : StrictPerfect X ⥤ FlasqueBoundedBelow.Obj X :=
  strictToBoundedBelow X ⋙ FlasqueBoundedBelow.total X

/-- The functor retains the original complex, rather than a chosen strict model. -/
lemma strictTotal_obj (X : Scheme.{u}) (K : StrictPerfect X) :
    ((strictTotal X).obj K).obj = (godementTotal X).obj K.obj := rfl

/-- The actual totalized source retains each specified original strict lower bound. -/
lemma strictTotal_isStrictlyGE (X : Scheme.{u}) (K : StrictPerfect X) (a : ℤ)
    [K.obj.IsStrictlyGE a] : ((strictTotal X).obj K).obj.IsStrictlyGE a := by
  change ((godementTotal X).obj K.obj).IsStrictlyGE a
  exact godementTotal_isStrictlyGE K.obj a
    (fun n hn => CochainComplex.isZero_of_isStrictlyGE K.obj a n hn)


end Quillen.PerfectComplexes.ProjectiveLine.StrictPositiveRetraction
end
end
