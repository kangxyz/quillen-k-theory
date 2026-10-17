/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalSupportedDensity
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

/-!
# Original-map consumers of global supported perfect density

The tests retain actual retraction and inverse equations, affine-attachment
homology maps, finite-family induction without compact ambient base, arbitrary
further restrictions, empty source and support, and chain-level naturality.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.GlobalSupportedDensity

open Quillen
open PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves

/-- Literal original retract maps coexist with actual global support vanishing. -/
theorem original_supported_retract_maps {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U Z : X.Opens)
    (hU : IsCompact (U : Set X)) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.toScheme.Modules ℤ) (hE : locallyPerfect U.toScheme E)
    (hz : IsZero ((DerivedCategory.Q (C := (U.ι ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E))) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj P)) ∧
      ∃ (i : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
        (r : (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P) ⟶
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj E),
        i ≫ r = 𝟙 _ := by
  obtain ⟨P, hP, ⟨r⟩, hPZ⟩ := locallyPerfect_exists_global_supported_derived_retract U hU E hE Z hZ
    hz
  exact ⟨P, hP, hPZ, r.i, r.r, r.retract⟩

/-- The actual global supported object and actual perfect complement retain
both original derived inverse equations for the original source immersion. -/
theorem original_supported_complement_inverse {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E)
    (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (hz : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ), locallyPerfect X P
      ∧ locallyPerfect U C ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj P)) ∧
      ∃ e : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P) ≅
        (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ C),
        e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ := by
  obtain ⟨P, C, hP, hC, ⟨e⟩, hPZ⟩ :=
    locallyPerfect_exists_global_supported_perfect_complement_of_openImmersion j E hE Z hZ hz
  exact ⟨P, C, hP, hC, hPZ, e, e.hom_inv_id, e.inv_hom_id⟩

/-- The original local weak arrow in the supported attachment gives actual
homology isomorphisms in every integer degree. -/
theorem original_supported_attachment_homology {U V X : Scheme.{u}}
    [QuasiSeparatedSpace X] [CompactSpace U] [IsAffine V]
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hc : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E)
    (hz : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj P)) ∧
      ∃ u : E ⊞ E⟦(1 : ℤ)⟧ ⟶ (restrict j).obj P,
        QuasiIso u ∧ ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap u n) := by
  obtain ⟨P, hP, u, hu, hPZ⟩ :=
    exists_supported_perfect_extension_across_affine_openImmersion j k hc Z hZ E hE hz
  have := hu
  exact ⟨P, hP, hPZ, u, hu, fun n => inferInstance⟩

/-- Finite chart attachment needs only quasi-separated ambient X; the full
ambient compactness assumption enters only when extracting a finite cover. -/
theorem finite_supported_union_without_compact_base {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U Z : X.Opens) (hU : IsCompact (U : Set X)) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.toScheme.Modules ℤ) (hE : locallyPerfect U.toScheme E)
    (hz : IsZero ((DerivedCategory.Q (C := (U.ι ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E)))
    (s : Finset X.affineOpens) :
    ∃ (hUS : U ≤ U ⊔ s.sup (fun V => V.val))
      (P : CochainComplex (U ⊔ s.sup (fun V => V.val)).toScheme.Modules ℤ),
      locallyPerfect _ P ∧
      IsZero ((DerivedCategory.Q (C := ((U ⊔ s.sup (fun V => V.val)).ι ⁻¹ᵁ Z).toScheme.Modules)).obj
        ((restrict ((U ⊔ s.sup (fun V => V.val)).ι ⁻¹ᵁ Z).ι).obj P)) ∧
      Nonempty (Retract ((DerivedCategory.Q (C := U.toScheme.Modules)).obj E)
        ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
          ((restrict (X.homOfLE hUS)).obj P))) := by
  obtain ⟨hUS, P, hP, r, hPZ⟩ :=
    exists_supported_perfect_retract_on_finite_affine_union U hU E hE Z hZ hz s
  exact ⟨hUS, P, hP, hPZ, r⟩

/-- Global derived zero on the prescribed support persists after arbitrary
open restriction, without any compactness premise on the restricting source. -/
theorem original_supported_restriction {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U Z : X.Opens)
    (hU : IsCompact (U : Set X)) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.toScheme.Modules ℤ) (hE : locallyPerfect U.toScheme E)
    (hz : IsZero ((DerivedCategory.Q (C := (U.ι ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (U.ι ⁻¹ᵁ Z).ι).obj E)))
    {Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      IsZero ((DerivedCategory.Q (C := (f ⁻¹ᵁ Z).toScheme.Modules)).obj
        ((restrict (f ⁻¹ᵁ Z).ι).obj ((restrict f).obj P))) := by
  obtain ⟨P, hP, _, hPZ⟩ := locallyPerfect_exists_global_supported_derived_retract U hU E hE Z hZ hz
  exact ⟨P, hP, isZero_restrict_preimage_of_isZero f Z P hPZ⟩
/-- Empty support imposes no extra condition on the original local complex. -/
theorem empty_support_original_retract {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
    (hU : IsCompact (U : Set X)) (E : CochainComplex U.toScheme.Modules ℤ)
      (hE : locallyPerfect U.toScheme E) :
    ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
      Nonempty (Retract ((DerivedCategory.Q (C := U.toScheme.Modules)).obj E)
        ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))) ∧
      IsZero ((DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj P)) := by
  apply locallyPerfect_exists_global_supported_derived_retract U hU E hE ⊥ isCompact_empty
  rw [Scheme.Hom.preimage_bot]
  apply (DerivedCategory.Q (C := (⊥ : U.toScheme.Opens).toScheme.Modules)).map_isZero
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  have hz : IsZero (((restrict (⊥ : U.toScheme.Opens).ι).obj E).X i) := by
    rw [AlgebraicGeometry.Scheme.Modules.isZero_iff_stalks]
    intro x
    exact False.elim x.property
  exact hz.eq_of_src _ _

/-- Empty original source admits completely unrestricted all-sheaf terms,
while the actual global extension still vanishes on the specified support. -/
theorem empty_source_arbitrary_original_complex {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (Z : X.Opens)
    (hZ : IsCompact (Z : Set X)) (E : CochainComplex (⊥ : X.Opens).toScheme.Modules ℤ) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex (⊥ : X.Opens).toScheme.Modules ℤ),
      locallyPerfect X P ∧ locallyPerfect (⊥ : X.Opens).toScheme C ∧
      Nonempty ((DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj P) ≅
        (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj (E ⊞ C)) ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj P)) := by
  have hE : locallyPerfect (⊥ : X.Opens).toScheme E := fun x => False.elim x.property
  apply locallyPerfect_exists_global_supported_perfect_complement ⊥ isCompact_empty E hE Z hZ
  apply (DerivedCategory.Q (C := ((⊥ : X.Opens).ι ⁻¹ᵁ Z).toScheme.Modules)).map_isZero
  rw [IsZero.iff_id_eq_zero]
  ext i : 1
  have hz : IsZero (((restrict ((⊥ : X.Opens).ι ⁻¹ᵁ Z).ι).obj E).X i) := by
    rw [AlgebraicGeometry.Scheme.Modules.isZero_iff_stalks]
    intro x
    exact False.elim x.val.property
  exact hz.eq_of_src _ _

/-- The actual support-image comparison is natural on original chain maps,
independently of all compactness and perfection hypotheses. -/
theorem support_image_original_chain_square {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] (Z : X.Opens) {E L : CochainComplex Y.Modules ℤ} (g : E ⟶ L) :
    (restrict (supportImageIso f Z).hom).map ((restrict (supportImageOpen f Z).ι).map g) ≫
        (supportImageRestrictionNatIso f Z).hom.app L =
      (supportImageRestrictionNatIso f Z).hom.app E ≫ (restrict Z.ι).map ((restrict f).map g) :=
  (supportImageRestrictionNatIso f Z).hom.naturality g

end QuillenTest.GlobalSupportedDensity
