/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction

/-!
# Identity and composition of perfect restriction

The actual termwise restriction comparisons lift to strict and locally perfect full categories.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Termwise restriction along the identity is canonically the identity. -/
def restrictIdIso (X : Scheme.{u}) : restrict (𝟙 X) ≅ 𝟭 (CochainComplex X.Modules ℤ) :=
  NatIso.mapHomologicalComplex Scheme.Modules.restrictFunctorId (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)

/-- The geometric identity comparison lifts to strict perfect complexes. -/
def strictRestrictIdIso (X : Scheme.{u}) :
    strictRestrict (𝟙 X) ≅ 𝟭 (StrictPerfect X) :=
  Functor.fullyFaithfulCancelRight (strictPerfect X).ι
    (Functor.isoWhiskerLeft (strictPerfect X).ι (restrictIdIso X))

/-- The geometric composition comparison lifts to strict perfect complexes. -/
def strictRestrictCompIso {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    strictRestrict (i ≫ j) ≅ strictRestrict j ⋙ strictRestrict i :=
  Functor.fullyFaithfulCancelRight (strictPerfect V).ι
    (Functor.isoWhiskerLeft (strictPerfect X).ι (restrictCompIso i j).symm)

/-- The geometric identity comparison lifts to locally perfect complexes. -/
def perfectRestrictIdIso (X : Scheme.{u}) :
    perfectRestrict (𝟙 X) ≅ 𝟭 (Perfect X) :=
  Functor.fullyFaithfulCancelRight (locallyPerfect X).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (restrictIdIso X))

/-- The geometric composition comparison lifts to locally perfect complexes. -/
def perfectRestrictCompIso {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    perfectRestrict (i ≫ j) ≅ perfectRestrict j ⋙ perfectRestrict i :=
  Functor.fullyFaithfulCancelRight (locallyPerfect V).ι
    (Functor.isoWhiskerLeft (locallyPerfect X).ι (restrictCompIso i j).symm)

end Quillen.PerfectComplexes

end

end
