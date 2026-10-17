/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Restriction
/-! # Composition of the original bounded-below flat pullbacks

The comparison is induced by the geometric `pullbackComp` isomorphism. Both directions retain
its literal map and the installed right-derived composite units.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

/-- The original standard ambient derived categories. -/
local instance flatCompositionStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _

variable {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X) [Flat k] [Flat j]

/-- The inverse comparison retains the same original units and inverse geometric map. -/
theorem derivedFlatPullbackPlusCompIso_inv_unit (K : CochainComplex.Plus X.Modules) :
    (Scheme.Modules.pullback (k ≫ j)).rightDerivedFunctorPlusUnit.app K ≫
      (derivedFlatPullbackPlusCompIso k j).inv.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp k j)).inv.app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback j)
        (Scheme.Modules.pullback k)).app K := by
  apply (cancel_mono ((derivedFlatPullbackPlusCompIso k j).hom.app
    (DerivedCategory.Plus.Q.obj K))).mp
  erw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
    Category.assoc, derivedFlatPullbackPlusCompIso_unit]
  erw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

end AlgebraicGeometry.Scheme.Modules
