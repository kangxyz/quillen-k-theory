/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.QuasiIsoOnBasis
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.PrincipalSections

/-!
# The literal affine counit from original principal section comparisons

If every original scalar-localized section comparison is a quasi-isomorphism,
then the literal associated-sections counit is a quasi-isomorphism. Actual
principal-section isomorphisms and their naturality identify this with the
basis criterion. Quasicoherence of every original homology sheaf is then a
CONCLUSION. No quasicoherence, boundedness or injectivity is assumed of the
input complex; the displayed principal-comparison premise must be proved by
geometry in applications.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
local instance (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).Additive :=
  AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_additive _


lemma quasiIso_of_affineSections_on_principals (R : CommRingCat.{u})
    {K L : CochainComplex (Spec R).Modules ℤ} (f : K ⟶ L)
    (hf : ∀ r : R, QuasiIso
      (((affineSectionsAt R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex (.up ℤ)).map f)) :
    QuasiIso f := by
  apply AlgebraicGeometry.Scheme.Modules.quasiIso_of_sections_on_principals R f
  intro r
  let := hf r
  change QuasiIso (((forget₂ (ModuleCat R) AddCommGrpCat).mapHomologicalComplex (.up ℤ)).map
    (((affineSectionsAt R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex (.up ℤ)).map f))
  infer_instance

lemma quasiIso_associatedSectionsCounit_of_principalComparisons (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ)
    (hK : ∀ r : R, QuasiIso (principalSectionsScalarComplexComparison R r K)) :
    QuasiIso (associatedSectionsCounit R K) := by
  apply quasiIso_of_affineSections_on_principals R
  intro r
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  let S := (ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).mapHomologicalComplex
    (.up ℤ)
  let e := NatIso.mapHomologicalComplex (principalRestrictionSectionsIso R r) (.up ℤ)
  let t := (NatIso.mapHomologicalComplex
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.localizationRestrictionNatIso R r)
    (.up ℤ)).hom.app ((sectionsComplex R).obj K)
  have ht : IsIso (S.map t) := by dsimp [t, S]; infer_instance
  have h : QuasiIso (S.map (principalSectionsComplexComparison R r K)) := by
    have := hK r
    exact (quasiIso_iff_comp_right _ (e.hom.app K)).mp (by
      simpa only [principalSectionsScalarComplexComparison_eq] using this)
  rw [principalSectionsComplexComparison_eq, Functor.map_comp] at h
  have hε : QuasiIso (S.map ((sectionsComplex (CommRingCat.of (Localization.Away r))).map
      ((restrict j).map (associatedSectionsCounit R K)))) :=
    (quasiIso_iff_comp_left (S.map t) _).mp h
  rw [← quasiIso_iff_comp_left (e.hom.app _), ← e.hom.naturality]
  apply (quasiIso_iff_comp_right _ (e.hom.app K)).mpr
  exact hε

lemma quasicoherent_homology_of_principalComparisons (R : CommRingCat.{u})
    (K : CochainComplex (Spec R).Modules ℤ)
    (hK : ∀ r : R, QuasiIso (principalSectionsScalarComplexComparison R r K)) (n : ℤ) :
    (K.homology n).IsQuasicoherent := by
  let := quasiIso_associatedSectionsCounit_of_principalComparisons R K hK
  have : IsIso (HomologicalComplex.homologyMap (associatedSectionsCounit R K) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  have hqc := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_homology
    ((associatedComplex R).obj ((sectionsComplex R).obj K)) (fun i => by
      change ((tilde.functor R).obj _).IsQuasicoherent
      infer_instance) n
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso (HomologicalComplex.homologyMap (associatedSectionsCounit R K) n)) hqc
end Quillen.PerfectComplexes.Affine
