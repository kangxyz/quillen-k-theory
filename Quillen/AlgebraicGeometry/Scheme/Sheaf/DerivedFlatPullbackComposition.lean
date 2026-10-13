/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChange
/-! # Composition of the original bounded-below flat pullbacks

The comparison is induced by the geometric `pullbackComp` isomorphism. Both directions retain
its literal map and the installed right-derived composite units.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.SchemeSheaf
/-- The original standard ambient derived categories. -/
local instance flatCompositionStandard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {U V X : Scheme.{u}} (k : U ⟶ V) (j : V ⟶ X) [Flat k] [Flat j]
/-- The original geometric pullback-composition comparison induces the derived comparison. -/
def derivedFlatPullbackPlusCompIso :
    derivedFlatPullbackPlus j ⋙ derivedFlatPullbackPlus k ≅
      derivedFlatPullbackPlus (k ≫ j) :=
  ((Scheme.Modules.pullback j).rightDerivedFunctorPlusCompIsoOfPreservesHomology
    (Scheme.Modules.pullback k)).symm ≪≫
  (Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback k).rightDerivedFunctorPlusIso
    (Scheme.Modules.pullbackComp k j)
/-- The actual comparison retains the literal pullback composition and installed units. -/
theorem derivedFlatPullbackPlusCompIso_unit (K : CochainComplex.Plus X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback j)
      (Scheme.Modules.pullback k)).app K ≫
      (derivedFlatPullbackPlusCompIso k j).hom.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (Scheme.Modules.pullbackComp k j)).hom.app K) ≫
      (Scheme.Modules.pullback (k ≫ j)).rightDerivedFunctorPlusUnit.app K := by
  let F := Scheme.Modules.pullback j
  let G := Scheme.Modules.pullback k
  have hc := F.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app G K
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app] at hc
  dsimp only [F, G] at hc
  change _ ≫ (_ ≫ _) = _
  rw [← hc, Category.assoc]
  simp only [Iso.symm_hom, Iso.hom_inv_id_app_assoc]
  exact (F ⋙ G).rightDerivedFunctorPlusIso_hom_app (Scheme.Modules.pullbackComp k j) K

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
end Quillen.SchemeSheaf
