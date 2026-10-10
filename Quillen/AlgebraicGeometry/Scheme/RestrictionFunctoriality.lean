/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# Functoriality of actual open restriction on scheme K- and G-theory

The identity and composition comparisons for module-sheaf restriction lift
through the fully faithful vector-bundle and coherent-sheaf inclusions.
Natural-isomorphism invariance of the zero-normalized small-model K-map then
gives strict functoriality of the existing public restriction maps. Only open
immersions occur; no pullback on coherent G-theory for general scheme maps is
asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- The geometric identity comparison lifts to actual vector bundles. -/
def vectorBundleRestrictIdIso (X : Scheme.{u}) :
    vectorBundleRestrict (𝟙 X) ≅ 𝟭 (FiniteLocallyFree X) :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree X).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι Scheme.Modules.restrictFunctorId)

/-- The geometric composition comparison lifts to actual vector bundles. -/
def vectorBundleRestrictCompIso {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    vectorBundleRestrict (i ≫ j) ≅ vectorBundleRestrict j ⋙ vectorBundleRestrict i :=
  Functor.fullyFaithfulCancelRight (finiteLocallyFree V).ι
    (Functor.isoWhiskerLeft (finiteLocallyFree X).ι
      (Scheme.Modules.restrictFunctorComp i j))

end Quillen.SchemeSheaf

namespace Quillen.CoherentScheme

/-- The geometric identity comparison lifts to actual coherent sheaves. -/
def coherentRestrictionIdIso (X : Scheme.{u}) [IsLocallyNoetherian X] :
    finiteTypeSheavesRestriction (𝟙 X) ≅ 𝟭 (FiniteTypeSheaves X) :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules X)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X) Scheme.Modules.restrictFunctorId)

/-- The geometric composition comparison lifts to actual coherent sheaves. -/
def coherentRestrictionCompIso {V U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    finiteTypeSheavesRestriction (i ≫ j) ≅
      finiteTypeSheavesRestriction j ⋙ finiteTypeSheavesRestriction i :=
  Functor.fullyFaithfulCancelRight (finiteTypeSheavesToModules V)
    (Functor.isoWhiskerLeft (finiteTypeSheavesToModules X)
      (Scheme.Modules.restrictFunctorComp i j))

end Quillen.CoherentScheme

namespace Quillen.Scheme

/-- Actual restriction along the identity induces the identity on K-theory. -/
@[simp high]
theorem restrictK_id (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    restrictK (𝟙 X) n = MonoidHom.id (K X n) := by
  change (SchemeSheaf.vectorBundleExactRestrict (𝟙 X)).smallKMap n = _
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := SchemeSheaf.vectorBundleExactRestrict (𝟙 X))
    (G := ExactFunctor.id (SchemeSheaf.vectorBundleExactStructure X))
    (SchemeSheaf.vectorBundleRestrictIdIso X) n).trans
    (ExactFunctor.smallKMap_id _ n)

/-- Actual restriction is contravariantly compatible with composition on K-theory. -/
@[simp high]
theorem restrictK_comp {V U X : AlgebraicGeometry.Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictK (i ≫ j) n = (restrictK i n).comp (restrictK j n) := by
  change (SchemeSheaf.vectorBundleExactRestrict (i ≫ j)).smallKMap n = _
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := SchemeSheaf.vectorBundleExactRestrict (i ≫ j))
    (G := (SchemeSheaf.vectorBundleExactRestrict j).comp
      (SchemeSheaf.vectorBundleExactRestrict i))
    (SchemeSheaf.vectorBundleRestrictCompIso i j) n).trans
    (ExactFunctor.smallKMap_comp _ _ n)

/-- Actual restriction along the identity induces the identity on G-theory. -/
@[simp high]
theorem restrictG_id (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X]
    (n : ℕ) : restrictG (𝟙 X) n = MonoidHom.id (G X n) := by
  change (CoherentScheme.coherentRestrictionExact (𝟙 X)).smallKMap n = _
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := CoherentScheme.coherentRestrictionExact (𝟙 X))
    (G := ExactFunctor.id (CoherentScheme.coherentExactStructure X))
    (CoherentScheme.coherentRestrictionIdIso X) n).trans
    (ExactFunctor.smallKMap_id _ n)

/-- Actual restriction is contravariantly compatible with composition on G-theory. -/
@[simp high]
theorem restrictG_comp {V U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictG (i ≫ j) n = (restrictG i n).comp (restrictG j n) := by
  change (CoherentScheme.coherentRestrictionExact (i ≫ j)).smallKMap n = _
  exact (ExactFunctor.smallKMap_eq_of_natIso
    (F := CoherentScheme.coherentRestrictionExact (i ≫ j))
    (G := (CoherentScheme.coherentRestrictionExact j).comp
      (CoherentScheme.coherentRestrictionExact i))
    (CoherentScheme.coherentRestrictionCompIso i j) n).trans
    (ExactFunctor.smallKMap_comp _ _ n)

end Quillen.Scheme
