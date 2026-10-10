/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Affine.StrictModuleModel
import Quillen.PerfectComplexes.DerivedStructure
import Quillen.Scheme.Coherent.Affine.Exact

/-!
# The actual affine derived comparison and termwise quasicoherent acyclicity

The associated-sheaf functor induces a triangulated functor from the actual
module derived category to the actual sheaf derived category. This file also
proves conservativity, quasicoherent homology of its image, compatibility with
actual principal derived restriction, and preservation and reflection of
quasi-isomorphisms by sections for complexes with quasicoherent terms.
No exactness of global sections on arbitrary sheaves is asserted. Full
faithfulness of the derived comparison and replacement of arbitrary complexes
with quasicoherent cohomology remain separate geometric theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.PerfectComplexes.Affine

/-- The exact associated-sheaf functor detects the actual quasi-isomorphisms. -/
theorem quasiIso_associated_iff (R : CommRingCat.{u})
    {K L : ModuleComplex R} (f : K ⟶ L) :
    QuasiIso ((associatedComplex R).map f) ↔ QuasiIso f :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (tilde.functor R)

/-- Naturality of the actual affine reconstruction on termwise quasicoherent
complexes. -/
@[reassoc]
theorem associatedSectionsIsoOfQuasicoherent_naturality (R : CommRingCat.{u})
    {K L : Complex (Spec R)} (hK : ∀ i, (K.X i).IsQuasicoherent)
    (hL : ∀ i, (L.X i).IsQuasicoherent) (f : K ⟶ L) :
    (associatedComplex R).map ((sectionsComplex R).map f) ≫
      (associatedSectionsIsoOfQuasicoherent R L hL).hom =
    (associatedSectionsIsoOfQuasicoherent R K hK).hom ≫ f := by
  ext i : 1
  exact Scheme.Modules.fromTildeΓNatTrans.naturality (f.f i)

/-- Actual global sections preserve and reflect quasi-isomorphisms between
termwise quasicoherent complexes on an affine scheme. -/
theorem quasiIso_sections_iff (R : CommRingCat.{u})
    {K L : Complex (Spec R)} (hK : ∀ i, (K.X i).IsQuasicoherent)
    (hL : ∀ i, (L.X i).IsQuasicoherent) (f : K ⟶ L) :
    QuasiIso ((sectionsComplex R).map f) ↔ QuasiIso f := by
  rw [← quasiIso_associated_iff R]
  rw [← quasiIso_iff_comp_right _
    (associatedSectionsIsoOfQuasicoherent R L hL).hom]
  rw [associatedSectionsIsoOfQuasicoherent_naturality R hK hL f]
  exact quasiIso_iff_comp_left _ _

/-- Associated sheaf complexes are acyclic exactly when the module complex
is acyclic. This uses exactness and faithfulness of tilde. -/
theorem acyclic_associated_iff (R : CommRingCat.{u}) (K : ModuleComplex R) :
    ((associatedComplex R).obj K).Acyclic ↔ K.Acyclic := by
  constructor
  · intro h i
    exact Functor.reflects_exact_of_faithful (tilde.functor R) (K.sc i) (h i)
  · intro h i
    exact (show (K.sc i).Exact from h i).map (tilde.functor R)

/-- Termwise quasicoherent affine acyclicity is detected by the genuine
complex of global sections. This is not an assertion about arbitrary terms. -/
theorem acyclic_sections_iff (R : CommRingCat.{u}) (K : Complex (Spec R))
    (hK : ∀ i, (K.X i).IsQuasicoherent) :
    ((sectionsComplex R).obj K).Acyclic ↔ K.Acyclic := by
  rw [← acyclic_associated_iff R]
  let e := associatedSectionsIsoOfQuasicoherent R K hK
  simp only [HomologicalComplex.acyclic_iff]
  exact forall_congr' fun i => ShortComplex.exact_iff_of_iso
    ((HomologicalComplex.shortComplexFunctor _ _ i).mapIso e)

local instance standardDerivedModules (R : Type u) [Ring R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

local instance standardDerivedSheaves (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The actual affine derived comparison, constructed from exact tilde.
Its target is the existing quasi-isomorphism localization of all sheaves. -/
abbrev associatedDerived (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat.{u} R) ⥤ Derived (Spec R) :=
  (tilde.functor R).mapDerivedCategory

/-- The comparison factors through the original sheaf localization functor. -/
def associatedDerivedFactors (R : CommRingCat.{u}) :
    DerivedCategory.Q ⋙ associatedDerived R ≅ associatedComplex R ⋙ toDerived (Spec R) :=
  (tilde.functor R).mapDerivedCategoryFactors

instance associatedDerived_commShift (R : CommRingCat.{u}) :
    (associatedDerived R).CommShift ℤ :=
  inferInstanceAs ((tilde.functor R).mapDerivedCategory.CommShift ℤ)

instance associatedDerived_isTriangulated (R : CommRingCat.{u}) :
    (associatedDerived R).IsTriangulated :=
  inferInstanceAs ((tilde.functor R).mapDerivedCategory.IsTriangulated)


/-- The actual affine derived comparison reflects isomorphisms between
localized module complexes. The proof uses genuine derived fractions and
reflection of quasi-isomorphisms by tilde. -/
theorem isIso_associatedDerived_map_iff (R : CommRingCat.{u})
    {K L : ModuleComplex R}
    (f : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    IsIso ((associatedDerived R).map f) ↔ IsIso f := by
  refine ⟨fun hf => ?_, fun hf => inferInstance⟩
  obtain ⟨M, g, s, hs, hfac⟩ := DerivedCategory.left_fac f
  have hgs : f ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map g := by
    rw [hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hg : IsIso ((associatedDerived R).map (DerivedCategory.Q.map g)) := by
    rw [← hgs, Functor.map_comp]
    infer_instance
  have hg' : IsIso ((toDerived (Spec R)).map ((associatedComplex R).map g)) :=
    (NatIso.isIso_map_iff (associatedDerivedFactors R) g).mp hg
  have : QuasiIso g := (quasiIso_associated_iff R g).mp
    ((DerivedCategory.isIso_Q_map_iff_quasiIso (Spec R).Modules _).mp hg')
  rw [hfac]
  infer_instance

/-- Conservativity of the actual affine derived comparison. No fullness
or faithfulness on derived morphisms is inferred from this property. -/
instance associatedDerived_reflectsIsomorphisms (R : CommRingCat.{u}) :
    (associatedDerived R).ReflectsIsomorphisms where
  reflects {K L} f hf := by
    let eK := (DerivedCategory.Q (C := ModuleCat.{u} R)).objObjPreimageIso K
    let eL := (DerivedCategory.Q (C := ModuleCat.{u} R)).objObjPreimageIso L
    have : IsIso ((associatedDerived R).map (eK.hom ≫ f ≫ eL.inv)) := by
      simp only [Functor.map_comp]
      infer_instance
    have : IsIso (eK.hom ≫ f ≫ eL.inv) :=
      (isIso_associatedDerived_map_iff R _).mp inferInstance
    have : IsIso (f ≫ eL.inv) := IsIso.of_isIso_comp_left eK.hom _
    exact IsIso.of_isIso_comp_right f eL.inv


/-- The actual affine derived comparison computes homology by tilde on
module chain representatives. -/
def associatedDerivedHomologyIso (R : CommRingCat.{u}) (K : ModuleComplex R) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((associatedDerived R).obj (DerivedCategory.Q.obj K)) ≅
    (tilde.functor R).obj (K.homology i) :=
  (DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso
      ((associatedDerivedFactors R).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors (Spec R).Modules i).app
      ((associatedComplex R).obj K) ≪≫
    (K.sc i).mapHomologyIso (tilde.functor R)

/-- Every object in the actual affine comparison's image has quasicoherent
cohomology. The converse essential-image assertion remains geometric. -/
theorem associatedDerived_quasicoherent_homology (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((associatedDerived R).obj K)).IsQuasicoherent := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} R)
  let e := Q.objObjPreimageIso K
  let e' := (associatedDerivedHomologyIso R (Q.objPreimage K) i).symm ≪≫
    (DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso
      ((associatedDerived R).mapIso e)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e' inferInstance


/-- Actual scalar localization on module derived categories. -/
abbrev principalDerivedLocalization (R : CommRingCat.{u}) (r : R) :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (Localization.Away r)) :=
  (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).mapDerivedCategory

/-- On chain objects, scalar localization followed by the affine derived
comparison agrees with the original geometric derived restriction. -/
def principalDerivedComparisonFactors (R : CommRingCat.{u}) (r : R) :
    DerivedCategory.Q ⋙ (principalDerivedLocalization R r ⋙
      associatedDerived (CommRingCat.of (Localization.Away r))) ≅
    DerivedCategory.Q ⋙ (associatedDerived R ⋙
      derivedRestrict (CoherentScheme.principalOpen R r)) := by
  let S := CommRingCat.of (Localization.Away r)
  let j := CoherentScheme.principalOpen R r
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let e₁ : DerivedCategory.Q ⋙ (principalDerivedLocalization R r ⋙ associatedDerived S) ≅
      Quillen.ModuleComplex.PrincipalLocalization.localize r (ComplexShape.up ℤ) ⋙
        (associatedComplex S ⋙ toDerived (Spec S)) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight F.mapDerivedCategoryFactors (associatedDerived S) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (associatedDerivedFactors S)
  let e₂ : DerivedCategory.Q ⋙ (associatedDerived R ⋙ derivedRestrict j) ≅
      associatedComplex R ⋙ (restrict j ⋙ toDerived (Spec S)) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (associatedDerivedFactors R) (derivedRestrict j) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedRestrictFactors j)
  exact e₁ ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (principalRestrictionAssociatedComplexIso R r) (toDerived (Spec S)) ≪≫
    Functor.associator _ _ _ ≪≫ e₂.symm

/-- The derived principal-localization comparison uses the original
`derivedRestrict`, rather than replacing the geometric functor. -/
def principalDerivedComparisonIso (R : CommRingCat.{u}) (r : R) :
    principalDerivedLocalization R r ⋙
      associatedDerived (CommRingCat.of (Localization.Away r)) ≅
    associatedDerived R ⋙ derivedRestrict (CoherentScheme.principalOpen R r) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    _ _ _ _ (principalDerivedComparisonFactors R r)

/-- The lifted comparison retains the specified chain-level comparison. -/
@[simp]
theorem principalDerivedComparisonIso_hom_app_Q_obj (R : CommRingCat.{u}) (r : R)
    (K : ModuleComplex R) :
    (principalDerivedComparisonIso R r).hom.app (DerivedCategory.Q.obj K) =
      (principalDerivedComparisonFactors R r).hom.app K := by
  simp [principalDerivedComparisonIso, Localization.liftNatIso,
    Localization.Lifting.iso]

end Quillen.PerfectComplexes.Affine
