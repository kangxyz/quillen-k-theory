/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Plus
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Shift

/-!
# Original flasque shifts and D-plus

The actual proof-forgetting shift and derived-shift comparisons retain the original underlying chain maps.
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
local instance coefficientStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The native Plus shift comparison lifted through its actual full inclusion. -/
def modelShiftPlusIso (X : Scheme.{u}) (n : ℤ) :
    modelShift X n ⋙ toPlus X ≅ toPlus X ⋙ shiftFunctor (CochainComplex.Plus X.Modules) n :=
  Functor.fullyFaithfulCancelRight (CochainComplex.Plus.ι X.Modules)
    (Functor.isoWhiskerLeft (toPlus X) ((CochainComplex.Plus.ι X.Modules).commShiftIso n).symm)

/-- Its underlying arrow is precisely the native inclusion-shift comparison. -/
lemma modelShiftPlusIso_hom_underlying (X : Scheme.{u}) (n : ℤ)
    (K : FlasqueBoundedBelow.Obj X) :
    ((modelShiftPlusIso X n).hom.app K).hom =
      ((CochainComplex.Plus.ι X.Modules).commShiftIso n).inv.app ((toPlus X).obj K) := by
  change (CochainComplex.Plus.ι X.Modules).map ((modelShiftPlusIso X n).hom.app K) = _
  rw [modelShiftPlusIso, Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
  rfl

/-- Native localization of the actual standard original shift. -/
def modelShiftDerivedIso (X : Scheme.{u}) (n : ℤ) :
    modelShift X n ⋙ toPlus X ⋙ DerivedCategory.Plus.Q ≅
      toPlus X ⋙ DerivedCategory.Plus.Q ⋙ shiftFunctor (DerivedCategory.Plus X.Modules) n :=
  Functor.isoWhiskerRight (modelShiftPlusIso X n) DerivedCategory.Plus.Q ≪≫
    Functor.isoWhiskerLeft (toPlus X) (DerivedCategory.Plus.Q.commShiftIso n)


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueCoefficients
end
end
