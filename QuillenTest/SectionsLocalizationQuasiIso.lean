/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionsLocalizationQuasiIso

/-! Actual original-map consumers of localization on a principal chart. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
  Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace QuillenTest.SectionsLocalizationQuasiIso

open Quillen

variable {R : CommRingCat.{u}} (r q : R) (I : Complex (Spec R)) (a : ℤ)
  (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
  (hqc : ∀ n, (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R q)).obj
    I).homology n).IsQuasicoherent)

/- Every original homology map is an isomorphism, with no global QC assumption. -/
include hbound hinj hqc in
lemma original_homology_map_isIso (n : ℤ) :
    IsIso (homologyMap (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I) n)
      := by
  let := quasiIso_sectionsLocalizationComplexComparison_basicOpen r q I a hbound hinj hqc
  infer_instance

/- The homology-level isomorphism factors the original restriction through the
actual localization numerator; no unnamed comparison is substituted. -/
lemma original_homology_numerator_equation (n : ℤ) :
    homologyMap ((NatTrans.mapHomologicalComplex (scalarLocalizeUnit R r) (.up ℤ)).app
        (affineSectionsComplex R (PrimeSpectrum.basicOpen q) I)) n ≫
      homologyMap (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I) n =
    homologyMap (affineSectionsComplexRestriction R
      (inf_le_left : PrimeSpectrum.basicOpen q ⊓ PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen
        q) I) n := by
  rw [← homologyMap_comp, sectionsLocalizationComplexComparison_unit]

/- The actual inverse homology map has both literal inverse laws. -/
include hbound hinj hqc in
lemma original_homology_inverse (n : ℤ) :
    ∃ g, homologyMap (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I) n ≫ g
      = 𝟙 _ ∧
      g ≫ homologyMap (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I) n =
        𝟙 _ := by
  let := original_homology_map_isIso r q I a hbound hinj hqc n
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/- Localizing at zero is included in the actual chart comparison. -/
include hbound hinj hqc in
lemma zero_localization :
    QuasiIso (sectionsLocalizationComplexComparison R 0 (PrimeSpectrum.basicOpen q) I) :=
  quasiIso_sectionsLocalizationComplexComparison_basicOpen 0 q I a hbound hinj hqc

/- On locally QC sheaves the exact same original localization lift is an isomorphism. -/
lemma original_degreewise_comparison (M : (Spec R).Modules)
    [(M.restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
      q)).IsQuasicoherent] :
    IsIso (sectionsLocalizationLift R r (PrimeSpectrum.basicOpen q) M) :=
  isIso_sectionsLocalizationLift_basicOpen r q M

end QuillenTest.SectionsLocalizationQuasiIso
