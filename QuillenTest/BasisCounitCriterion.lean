/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.CounitCriterion

/-! # Consumers of original basis detection and the actual affine counit -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.BasisCounitCriterion

/-- Genuine local section exactness solves cycles in every original stalk. -/
theorem original_stalk_cycles {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hS : ∀ U ∈ B, (S.map (Quillen.SheafCohomology.sectionsFunctor U)).Exact) (x : X) :
    ∀ z, (S.map ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))).g z = 0 →
      ∃ a, (S.map ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))).f a = z := by
  have h := Quillen.SheafCohomology.exact_of_sections_on_basis S hB hS
  have hx := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp h x
  exact (ShortComplex.ab_exact_iff _).mp hx

/-- No boundedness assumption is needed to annihilate the original homology. -/
theorem original_homology_vanishes {X : TopCat.{u}}
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℤ)
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (hK : ∀ U ∈ B, (Quillen.SheafCohomology.sectionsComplex K U).Acyclic) (n : ℤ) :
    IsZero (K.homology n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    (Quillen.SheafCohomology.acyclic_of_sections_on_basis K hB hK n)

/-- The original map on homology is invertible after section-basis detection. -/
theorem original_homology_map {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (f : K ⟶ L) {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso ((Quillen.SchemeSheaf.sectionsComplex X U).map f)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap f n) := by
  let := Quillen.SchemeSheaf.quasiIso_of_sections_on_basis f hB hf
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance

/-- Actual chain composition can be canceled after checking the original basis maps. -/
theorem original_composition_cancels {X : Scheme.{u}}
    {K L M : CochainComplex X.Modules ℤ} (f : K ⟶ L) (g : L ⟶ M)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso ((Quillen.SchemeSheaf.sectionsComplex X U).map f))
    (hfg : ∀ U ∈ B, QuasiIso ((Quillen.SchemeSheaf.sectionsComplex X U).map (f ≫ g))) :
    QuasiIso g := by
  let := Quillen.SchemeSheaf.quasiIso_of_sections_on_basis f hB hf
  exact (quasiIso_iff_comp_left f g).mp
    (Quillen.SchemeSheaf.quasiIso_of_sections_on_basis (f ≫ g) hB hfg)

open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine

/-- The inverse is for the unchanged original affine counit homology map. -/
theorem original_counit_homology_inverse (R : CommRingCat.{u}) (K : Complex (Spec R))
    (hK : ∀ r : R, QuasiIso (principalSectionsScalarComplexComparison R r K)) (n : ℤ) :
    ∃ t, HomologicalComplex.homologyMap (associatedSectionsCounit R K) n ≫ t = 𝟙 _ ∧
      t ≫ HomologicalComplex.homologyMap (associatedSectionsCounit R K) n = 𝟙 _ := by
  let := quasiIso_associatedSectionsCounit_of_principalComparisons R K hK
  have : IsIso (HomologicalComplex.homologyMap (associatedSectionsCounit R K) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- Both genuine module reconstruction and original QC homology follow from the comparisons. -/
theorem original_derived_model_and_homology (R : CommRingCat.{u}) (K : Complex (Spec R))
    (hK : ∀ r : R, QuasiIso (principalSectionsScalarComplexComparison R r K)) :
    IsIso ((toDerived (Spec R)).map (associatedSectionsCounit R K)) ∧
      ∀ n : ℤ, (K.homology n).IsQuasicoherent := by
  let := quasiIso_associatedSectionsCounit_of_principalComparisons R K hK
  exact ⟨inferInstance, quasicoherent_homology_of_principalComparisons R K hK⟩

end QuillenTest.BasisCounitCriterion
