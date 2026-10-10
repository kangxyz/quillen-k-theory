/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedExtensionByZero

/-!
# Actual derived restriction along a scheme isomorphism

The original module restrictions along inverse scheme maps form an actual
equivalence, with the original complex restriction as its literal induced
functor. The genuine chain adjunction then has invertible counit, and the
proved derived unit/counit formulas yield full faithfulness of the original
derived restriction. Both arbitrary derived arrows and the endpoint-normalized
original chain-derived arrows retain zero reflection, including shifted sources.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}}

/-- The actual module restrictions along inverse scheme isomorphisms are inverse functors. -/
def moduleRestrictEquivalenceOfIso (e : U ≅ X) : X.Modules ≌ U.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId).symm
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

variable (j : U ⟶ X) [IsIso j] [IsOpenImmersion j]

/-- The equivalence retains the literal original complex restriction functor. -/
def restrictEquivalenceOfIso : Complex X ≌ Complex U :=
  (moduleRestrictEquivalenceOfIso (asIso j)).mapHomologicalComplex (.up ℤ)

local instance restrictIsEquivalenceOfIso : (restrict j).IsEquivalence :=
  (restrictEquivalenceOfIso j).isEquivalence_functor

/-- Along a genuine scheme isomorphism the original chain extension counit is an isomorphism. -/
instance extensionByZero_counit_isIso_of_isIso : IsIso (extensionByZeroAdjunction j).counit := by
  infer_instance

/-- The derived counit is invertible on every ambient derived object, using original localization.
-/
instance derivedExtensionByZero_counit_app_isIso_of_isIso (L : Derived X) :
    IsIso ((derivedExtensionByZeroAdjunction j).counit.app L) := by
  let : (toDerived X).EssSurj := Localization.essSurj _
    (HomologicalComplex.quasiIso X.Modules (.up ℤ))
  rw [← NatTrans.isIso_app_iff_of_iso (derivedExtensionByZeroAdjunction j).counit
    ((toDerived X).objObjPreimageIso L)]
  rw [derivedExtensionByZeroAdjunction_counit_app]
  infer_instance

instance derivedExtensionByZero_counit_isIso_of_isIso :
    IsIso (derivedExtensionByZeroAdjunction j).counit :=
  NatIso.isIso_of_isIso_app _

/-- Original derived restriction along a scheme isomorphism is genuinely fully faithful. -/
def derivedRestrictFullyFaithfulOfIsIso : (derivedRestrict j).FullyFaithful :=
  (derivedExtensionByZeroAdjunction j).fullyFaithfulROfIsIsoCounit

instance derivedRestrict_faithful_of_isIso : (derivedRestrict j).Faithful :=
  (derivedRestrictFullyFaithfulOfIsIso j).faithful

/-- Zero reflection holds for every ambient derived map, including arbitrary shifted endpoints. -/
lemma derivedRestrict_map_eq_zero_iff {K L : Derived X} (φ : K ⟶ L) :
    (derivedRestrict j).map φ = 0 ↔ φ = 0 := by
  rw [← (derivedRestrict j).map_zero]
  exact (derivedRestrict j).map_injective.eq_iff

/-- The normalized original localization endpoints retain the same zero reflection. -/
lemma restrictDerivedHom_eq_zero_iff {K L : Complex X}
    (φ : (toDerived X).obj K ⟶ (toDerived X).obj L) :
    restrictDerivedHom j φ = 0 ↔ φ = 0 := by
  rw [restrictDerivedHom, ← cancel_epi ((derivedRestrictFactors j).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc, comp_zero]
  rw [← cancel_mono ((derivedRestrictFactors j).inv.app L)]
  simp only [Category.assoc, Iso.hom_inv_id_app, zero_comp]
  erw [Category.comp_id]
  exact derivedRestrict_map_eq_zero_iff j φ

end Quillen.PerfectComplexes
