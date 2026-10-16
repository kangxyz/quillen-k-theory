/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenModuleReconstruction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! Consumers retain original chain arrows, exact term bounds and both derived equations. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
open Quillen.PerfectComplexes.Affine
namespace QuillenTest.OpenModuleReconstruction

open Quillen

lemma literal_original_comparison (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (I : CochainComplex W.toScheme.Modules ℤ) (c : ℤ) :
    openPushforwardSectionsTruncationComparison R W I c =
      (restrict W.ι).map
        ((associatedComplex R).map
          (((sectionsComplex R).obj ((pushforwardComplex W.ι).obj I)).ιTruncLE c) ≫
          associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) ≫
        ((pushforwardComplexRestrictIso W.ι).app I).hom := rfl

lemma exact_term_support {R : CommRingCat.{u}} (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (I : CochainComplex W.toScheme.Modules ℤ) (a c : ℤ)
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
    (hW : IsCompact (W : Set (Spec R))) (E : CochainComplex W.toScheme.Modules ℤ) (a b : ℤ)
    [E.IsGE a] [E.IsLE b] (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (I : CochainComplex W.toScheme.Modules ℤ) (q : E ⟶ I) (c : ℤ),
      (∀ n, IsIso (homologyMap q n)) ∧
      (∀ n, IsIso (homologyMap (openPushforwardSectionsTruncationComparison R W I c) n)) := by
  obtain ⟨I, q, c, hI, hi, hq, hPa, hPc, hφ⟩ :=
    exists_bounded_module_open_roof R W hW E a b hqc
  let := hq
  let := hφ
  exact ⟨I, q, c, fun n => inferInstance, fun n => inferInstance⟩

lemma both_original_derived_equations (R : CommRingCat.{u}) (W : (Spec R).Opens)
    [HasDerivedCategory.{v} W.toScheme.Modules]
    {E I : CochainComplex W.toScheme.Modules ℤ} (q : E ⟶ I) (c : ℤ) [QuasiIso q]
    [QuasiIso (openPushforwardSectionsTruncationComparison R W I c)] :
    (openModuleReconstructionIso R W q c).hom ≫ (DerivedCategory.Q (C := W.toScheme.Modules)).map q
      =
      (DerivedCategory.Q (C := W.toScheme.Modules)).map
        (openPushforwardSectionsTruncationComparison R W I c) ∧
    (openModuleReconstructionIso R W q c).inv ≫
        (DerivedCategory.Q (C := W.toScheme.Modules)).map
          (openPushforwardSectionsTruncationComparison R W I c) =
      (DerivedCategory.Q (C := W.toScheme.Modules)).map q :=
  ⟨openModuleReconstructionIso_hom_comp R W q c, openModuleReconstructionIso_inv_comp R W q c⟩

lemma reconstructed_source_is_locallyPerfect (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) [HasDerivedCategory.{v} W.toScheme.Modules]
    {E : CochainComplex W.toScheme.Modules ℤ} (hE : locallyPerfect W.toScheme E) :
    ∃ (P : ModuleComplex R) (a c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      locallyPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj P)) := by
  -- The conclusion is model-free; this transport API uses the standard derived model.
  obtain ⟨P, a, c, hPa, hPc, ⟨e⟩⟩ :=
    @locallyPerfect_exists_bounded_module_open_representative.{u, u + 1} R W hW
      (Scheme.Modules.standardHasDerivedCategory W.toScheme) E hE
  exact ⟨P, a, c, hPa, hPc, (locallyPerfect_iff_of_derivedIso e).mpr hE⟩

lemma empty_open_original_model (R : CommRingCat.{u})
    [HasDerivedCategory.{v} (⊥ : (Spec R).Opens).toScheme.Modules]
    (E : CochainComplex (⊥ : (Spec R).Opens).toScheme.Modules ℤ) :
    ∃ (P : ModuleComplex R) (a c : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE c ∧
      Nonempty ((DerivedCategory.Q (C := (⊥ : (Spec R).Opens).toScheme.Modules)).obj
          ((restrict (⊥ : (Spec R).Opens).ι).obj ((associatedComplex R).obj P)) ≅
        (DerivedCategory.Q (C := (⊥ : (Spec R).Opens).toScheme.Modules)).obj E) := by
  have hE : locallyPerfect (⊥ : (Spec R).Opens).toScheme E := by
    intro x
    exact (show False from x.2).elim
  exact locallyPerfect_exists_bounded_module_open_representative R ⊥ isCompact_empty hE

end QuillenTest.OpenModuleReconstruction
