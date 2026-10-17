/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.PushforwardExactness
public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-!
# Lower-bounded flasque perfect complexes in D-plus

The proof-forgetting functor retains the actual lower-bounded complex. For any original scheme
map, its installed direct-image unit is invertible on these flasque inputs.
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
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
/-- The standard derived-category instance for sheaves of modules on `X`. -/
local instance standardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Forget only the perfect/flasque proofs, retaining the original lower-bounded complex. -/
def toPlus (X : Scheme.{u}) : FlasqueBoundedBelow.Obj X ⥤ CochainComplex.Plus X.Modules :=
  ObjectProperty.lift _ (FlasqueBoundedBelow.objects X).ι (fun K => K.property.1.2)

/-- The actual installed direct-image unit, naturally restricted to the flasque model. -/
def derivedUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    toPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⟶
      toPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f :=
  CategoryTheory.Functor.whiskerLeft (toPlus X) (derivedPushforwardPlusUnit f)

instance derivedUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (derivedUnit f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  exact isIso_derivedPushforwardPlusUnit_of_flasque f ((toPlus X).obj K) K.property.2

/-- Natural derived comparison using the original installed unit, with no chosen models. -/
def derivedPushforwardIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    toPlus X ⋙ (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ≅
      toPlus X ⋙ DerivedCategory.Plus.Q ⋙ derivedPushforwardPlus f := asIso (derivedUnit f)


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
end
end
