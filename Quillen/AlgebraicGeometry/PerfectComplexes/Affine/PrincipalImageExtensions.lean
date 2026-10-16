/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalDerivedImage
public import Quillen.CategoryTheory.Abelian.ZeroPushout

/-!
# Genuine principal strict-image extension closure

Actual sections preserve original short exact sequences of explicitly
termwise quasicoherent affine complexes, proved by reflection through the faithful
associated-sheaf functor and its original reconstruction counit. The
constructed principal derived image then gives actual strict restriction
witnesses for extensions. Finally the genuine zero-pushout quotient adapter
retains the original strict Waldhausen cofibration and quotient arrows.
No exactness of sections on arbitrary sheaves or all-perfect enhancement
comparison is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- Actual affine sections preserve a short exact sequence whose three original
complexes have QC terms. The proof reflects exactness through faithful tilde
and its original counit, not exactness of sections on all sheaves. -/
lemma shortExact_sections_of_quasicoherent (R : CommRingCat.{u})
    (S : ShortComplex (CochainComplex (Spec R).Modules ℤ)) (hS : S.ShortExact)
    (h₁ : ∀ i, (S.X₁.X i).IsQuasicoherent)
    (h₂ : ∀ i, (S.X₂.X i).IsQuasicoherent)
    (h₃ : ∀ i, (S.X₃.X i).IsQuasicoherent) :
    (S.map (sectionsComplex R)).ShortExact := by
  let T := S.map (sectionsComplex R)
  let G := associatedComplex R
  let e : T.map G ≅ S := ShortComplex.isoMk
    (associatedSectionsIsoOfQuasicoherent R S.X₁ h₁)
    (associatedSectionsIsoOfQuasicoherent R S.X₂ h₂)
    (associatedSectionsIsoOfQuasicoherent R S.X₃ h₃)
    (by exact (associatedSectionsIsoOfQuasicoherent_naturality R h₁ h₂ S.f).symm)
    (by exact (associatedSectionsIsoOfQuasicoherent_naturality R h₂ h₃ S.g).symm)
  have hT : (T.map G).ShortExact := (ShortComplex.shortExact_iff_of_iso e).mpr hS
  exact { exact := Functor.reflects_exact_of_faithful G T hT.exact
          mono_f := Functor.mono_of_mono_map G hT.mono_f
          epi_g := Functor.epi_of_epi_map G hT.epi_g }

/-- Actual principal strict witnesses are closed under original short exact
sequences of termwise-QC target complexes. -/
lemma principal_strict_witness_extension (R : CommRingCat.{u}) (r : R)
    (S : ShortComplex (CochainComplex (Spec (.of (Localization.Away r))).Modules ℤ))
      (hS : S.ShortExact)
    (h₁ : ∀ i, (S.X₁.X i).IsQuasicoherent)
    (h₂ : ∀ i, (S.X₂.X i).IsQuasicoherent)
    (h₃ : ∀ i, (S.X₃.X i).IsQuasicoherent)
    (hA : ∃ (E : StrictPerfect (Spec R))
      (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        S.X₁), QuasiIso q)
    (hC : ∃ (E : StrictPerfect (Spec R))
      (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        S.X₃), QuasiIso q) :
    ∃ (E : StrictPerfect (Spec R))
      (q : (restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj E.obj ⟶
        S.X₂), QuasiIso q := by
  rw [exists_principal_strict_quasiIso_iff_moduleDerivedImage R r S.X₂ h₂]
  have hT := shortExact_sections_of_quasicoherent (.of (Localization.Away r)) S hS h₁ h₂ h₃
  exact (principalModuleDerivedImage R r).ext_of_isTriangulatedClosed₂
    (DerivedCategory.triangleOfSES hT) (DerivedCategory.triangleOfSES_distinguished hT)
    ((exists_principal_strict_quasiIso_iff_moduleDerivedImage R r S.X₁ h₁).mp hA)
    ((exists_principal_strict_quasiIso_iff_moduleDerivedImage R r S.X₃ h₃).mp hC)

/-- Original cofibration quotient squares give extension closure of the
literal principal strict witnessed-image predicate. -/
lemma principal_strict_image_extension (R : CommRingCat.{u}) (r : R)
    {A B Q : StrictPerfect (Spec (.of (Localization.Away r)))} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (strictWaldhausen _).cof i)
    (h : IsPushout i ((strictWaldhausen _).isZero.from_ A) q
      ((strictWaldhausen _).isZero.to_ Q))
    (hA : Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) A)
    (hQ : Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) Q) :
    Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) B := by
  let X := Spec (.of (Localization.Away r))
  let P := strictPerfect X
  have hp := Waldhausen.fullSubcategory_map_pushout
    (abelianExactStructure (CochainComplex X.Modules ℤ)) P hi h
  have : Mono i.hom := (Waldhausen.complexSubcategory_inclusion_exact P).cofibration i hi
  obtain ⟨w, hw⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    (P.ι.map_isZero (strictWaldhausen X).isZero) hp
  have hqc (E : StrictPerfect X) (n : ℤ) : (E.obj.X n).IsQuasicoherent := by
    let := E.property.2 n
    infer_instance
  obtain ⟨E, p, hp⟩ := principal_strict_witness_extension R r (ShortComplex.mk i.hom q.hom w)
    hw (hqc A) (hqc B) (hqc Q)
    (by obtain ⟨E, p, hp⟩ := hA; exact ⟨E, p.hom, hp⟩)
    (by obtain ⟨E, p, hp⟩ := hQ; exact ⟨E, p.hom, hp⟩)
  exact ⟨E, ObjectProperty.homMk p, hp⟩

end Quillen.PerfectComplexes.Affine
