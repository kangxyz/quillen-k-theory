/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenModuleReconstruction

/-! Consumers retain original chain arrows, exact term bounds and both derived equations. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace Quillen.Tests.OpenModuleReconstruction

lemma literal_original_comparison (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (I : Complex W.toScheme) (c : ℤ) :
    openPushforwardSectionsTruncationComparison R W I c =
      (restrict W.ι).map
        ((associatedComplex R).map
          (((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).ιTruncLE c) ≫
          associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) ≫
        ((pushforwardComplexRestrictIso W.ι).app I).hom := rfl

lemma exact_term_support {R : CommRingCat.{u}} (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (I : Complex W.toScheme) (a c : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent)
    [((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).IsLE c] :
    ∀ n, n < a ∨ c < n → IsZero ((openPushforwardSectionsTruncation R W I c).X n) := by
  obtain ⟨ha, hc, _⟩ := openPushforwardSectionsTruncation_bounds_quasiIso W hW I a c hbound hinj hqc
  intro n hn
  rcases hn with hn | hn
  · exact CochainComplex.isZero_of_isStrictlyGE _ a n hn
  · exact CochainComplex.isZero_of_isStrictlyLE _ c n hn

lemma actual_resolution_roof_homology (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme) (a b : ℤ)
    [E.IsGE a] [E.IsLE b] (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (I : Complex W.toScheme) (q : E ⟶ I) (c : ℤ),
      (∀ n, IsIso (homologyMap q n)) ∧
      (∀ n, IsIso (homologyMap (openPushforwardSectionsTruncationComparison R W I c) n)) := by
  obtain ⟨I, q, c, hI, hi, hq, hPa, hPc, hφ⟩ :=
    exists_bounded_module_open_roof R W hW E a b hqc
  let := hq
  let := hφ
  exact ⟨I, q, c, fun n => inferInstance, fun n => inferInstance⟩

lemma both_original_derived_equations (R : CommRingCat.{u}) (W : (Spec R).Opens)
    [HasDerivedCategory.{v} W.toScheme.Modules]
    {E I : Complex W.toScheme} (q : E ⟶ I) (c : ℤ) [QuasiIso q]
    [QuasiIso (openPushforwardSectionsTruncationComparison R W I c)] :
    (openModuleReconstructionIso R W q c).hom ≫ (toDerived W.toScheme).map q =
      (toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c) ∧
    (openModuleReconstructionIso R W q c).inv ≫
        (toDerived W.toScheme).map (openPushforwardSectionsTruncationComparison R W I c) =
      (toDerived W.toScheme).map q :=
  ⟨openModuleReconstructionIso_hom_comp R W q c, openModuleReconstructionIso_inv_comp R W q c⟩

lemma reconstructed_source_is_locallyPerfect (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) [HasDerivedCategory.{v} W.toScheme.Modules]
    {E : Complex W.toScheme} (hE : locallyPerfect W.toScheme E) :
    ∃ (P : ModuleComplex R) (a c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      locallyPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj P)) := by
  obtain ⟨P, a, c, hPa, hPc, ⟨e⟩⟩ :=
    locallyPerfect_exists_bounded_module_open_representative R W hW hE
  exact ⟨P, a, c, hPa, hPc, (locallyPerfect_iff_of_derivedIso e).mpr hE⟩

lemma empty_open_original_model (R : CommRingCat.{u})
    [HasDerivedCategory.{v} (⊥ : (Spec R).Opens).toScheme.Modules]
    (E : Complex (⊥ : (Spec R).Opens).toScheme) :
    ∃ (P : ModuleComplex R) (a c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      Nonempty ((toDerived (⊥ : (Spec R).Opens).toScheme).obj
          ((restrict (⊥ : (Spec R).Opens).ι).obj ((associatedComplex R).obj P)) ≅
        (toDerived (⊥ : (Spec R).Opens).toScheme).obj E) := by
  have hE : locallyPerfect (⊥ : (Spec R).Opens).toScheme E := by
    intro x
    exact (show False from x.2).elim
  exact locallyPerfect_exists_bounded_module_open_representative R ⊥ isCompact_empty hE

end Quillen.Tests.OpenModuleReconstruction
