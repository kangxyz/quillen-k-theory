/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionsLocalization

/-! # Exact-map consumers of principal and arbitrary-open section localization -/
@[expose] public section

open HomologicalComplex
open Quillen.PerfectComplexes


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  HomologicalComplex
open Quillen.PerfectComplexes.Affine
namespace QuillenTest.AffineSectionsLocalization

open Quillen

/-- The original principal-open section identification retains both inverse laws. -/
theorem original_principal_section_iso (R : CommRingCat.{u}) (r : R) (M : (Spec R).Modules) :
    (principalRestrictionSectionsIso R r).hom.app M ≫
      (principalRestrictionSectionsIso R r).inv.app M = 𝟙 _ ∧
    (principalRestrictionSectionsIso R r).inv.app M ≫
      (principalRestrictionSectionsIso R r).hom.app M = 𝟙 _ :=
  ⟨(principalRestrictionSectionsIso R r).hom_inv_id_app M,
    (principalRestrictionSectionsIso R r).inv_hom_id_app M⟩

/-- A numerator goes to its literal original restriction on the basic open. -/
theorem original_principal_numerator (R : CommRingCat.{u}) (r : R) (M : (Spec R).Modules)
    (x : moduleSpecΓFunctor.obj M) :
    (principalSectionsScalarComparison R r).app M
      ((moduleSpecΓFunctor.obj M).localizedModuleMkLinearMap (Submonoid.powers r) x) =
    ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op) x :=
  principalSectionsScalarComparison_mk R r M x

/-- The actual localization universal property characterizes the constructed map on every open. -/
theorem original_open_lift_unique (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (M : (Spec R).Modules)
    (q : (scalarLocalize R r).obj ((affineSectionsAt R V).obj M) ⟶
      (affineSectionsAt R (V ⊓ PrimeSpectrum.basicOpen r)).obj M)
    (hq : ∀ x, q (scalarLocalizeMk R r ((affineSectionsAt R V).obj M) x) =
      ((affineSectionsRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V)).app M) x) :
    q = sectionsLocalizationLift R r V M := by
  apply scalarLocalize_hom_ext R r (sectionsIntersection_units R r V M)
  intro x
  exact (hq x).trans (sectionsLocalizationLift_mk R r V M x).symm

/-- The full original restriction chain map factors through its actual localization numerator. -/
theorem original_unit_factorization (R : CommRingCat.{u}) (r : R) (V : (Spec R).Opens)
    (I : CochainComplex (Spec R).Modules ℤ) :
    (NatTrans.mapHomologicalComplex (scalarLocalizeUnit R r) (.up ℤ)).app
        (affineSectionsComplex R V I) ≫ sectionsLocalizationComplexComparison R r V I =
      affineSectionsComplexRestriction R (inf_le_left : V ⊓ PrimeSpectrum.basicOpen r ≤ V) I :=
  sectionsLocalizationComplexComparison_unit R r V I

/-- Shrinking arbitrary opens preserves the whole original chain-map square. -/
theorem original_shrinking_square (R : CommRingCat.{u}) (r : R)
    {U V : (Spec R).Opens} (h : U ≤ V) (I : CochainComplex (Spec R).Modules ℤ) :
    ((scalarLocalize R r).mapHomologicalComplex (.up ℤ)).map
        (affineSectionsComplexRestriction R h I) ≫ sectionsLocalizationComplexComparison R r U I =
    sectionsLocalizationComplexComparison R r V I ≫
      affineSectionsComplexRestriction R (inf_le_inf h le_rfl) I :=
  sectionsLocalizationComplexComparison_restrict R r h I

/-- Both original homology inverse laws survive localization at zero as well. -/
theorem original_zero_localization_homology (R : CommRingCat.{u})
    (I : CochainComplex (Spec R).Modules ℤ)
    (a n : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    ∃ p, homologyMap (principalSectionsScalarComplexComparison R 0 I) n ≫ p = 𝟙 _ ∧
      p ≫ homologyMap (principalSectionsScalarComplexComparison R 0 I) n = 𝟙 _ := by
  let := quasiIso_principalSectionsScalarComplexComparison 0 I a hbound hinj hqc
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- The generic actual localization map is weak at affine top, with an honest negative lower bound.
  -/
theorem original_affine_top (R : CommRingCat.{u}) (r : R) (I : CochainComplex (Spec R).Modules ℤ)
    (hbound : ∀ n, n < -7 → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (sectionsLocalizationComplexComparison R r ⊤ I) :=
  quasiIso_sectionsLocalizationComplexComparison_top r I (-7) hbound hinj hqc

end QuillenTest.AffineSectionsLocalization
