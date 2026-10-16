/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalDensity
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! Original-map, complement, restriction and empty-open consumers for global qcqs density. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts
namespace QuillenTest.GlobalPerfectDensity

open Quillen

lemma original_global_retraction_maps {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : CochainComplex U.toScheme.Modules ℤ)
    (hE : locallyPerfect U.toScheme E) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (i : (DerivedCategory.Q (C := U.toScheme.Modules)).obj E ⟶
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P))
        (r : (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P) ⟶
          (DerivedCategory.Q (C := U.toScheme.Modules)).obj E),
        i ≫ r = 𝟙 _ := by
  obtain ⟨P, hP, ⟨r⟩⟩ := locallyPerfect_exists_global_derived_retract U hU E hE
  exact ⟨P, hP, r.i, r.r, r.retract⟩

lemma original_perfect_complex_biproduct {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : CochainComplex U.toScheme.Modules ℤ)
    (hE : locallyPerfect U.toScheme E) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex U.toScheme.Modules ℤ), locallyPerfect X P
      ∧ locallyPerfect U.toScheme C ∧
      ∃ e : (DerivedCategory.Q (C := U.toScheme.Modules)).obj (E ⊞ C) ≅
        (DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict U.ι).obj P), e.hom ≫ e.inv
          = 𝟙 _ := by
  obtain ⟨P, C, hP, hC, ⟨e⟩⟩ := locallyPerfect_exists_global_perfect_complement U hU E hE
  exact ⟨P, C, hP, hC, e.symm, e.inv_hom_id⟩

lemma complement_preserves_original_split_mono {X : Scheme.{u}} {E P : CochainComplex X.Modules ℤ}
    (hE : locallyPerfect X E) (hP : locallyPerfect X P)
    (r : Retract ((DerivedCategory.Q (C := X.Modules)).obj E)
      ((DerivedCategory.Q (C := X.Modules)).obj P)) :
    ∃ (C : CochainComplex X.Modules ℤ), locallyPerfect X C ∧
      ∃ e : (DerivedCategory.Q (C := X.Modules)).obj P ≅ (DerivedCategory.Q (C := X.Modules)).obj
        (E ⊞ C),
        r.i = (DerivedCategory.Q (C := X.Modules)).map (biprod.inl : E ⟶ E ⊞ C) ≫ e.inv := by
  obtain ⟨C, hC, e, he⟩ := exists_actual_perfect_complement_of_derived_retract hE hP r
  exact ⟨C, hC, e, by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

lemma restriction_of_original_complement {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hVU : V ≤ U) (hU : IsCompact (U : Set X))
      (E : CochainComplex U.toScheme.Modules ℤ)
    (hE : locallyPerfect U.toScheme E) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex U.toScheme.Modules ℤ), locallyPerfect X P
      ∧ locallyPerfect U.toScheme C ∧
      Nonempty ((DerivedCategory.Q (C := V.toScheme.Modules)).obj ((restrict V.ι).obj P) ≅
        (DerivedCategory.Q (C := V.toScheme.Modules)).obj
          ((restrict (X.homOfLE hVU)).obj E ⊞ (restrict (X.homOfLE hVU)).obj C)) := by
  obtain ⟨P, C, hP, hC, ⟨e⟩⟩ := locallyPerfect_exists_global_perfect_complement U hU E hE
  let k := X.homOfLE hVU
  let : PreservesBinaryBiproducts (restrict k) := preservesBinaryBiproducts_of_preservesBiproducts _
  exact ⟨P, C, hP, hC, ⟨(DerivedCategory.Q (C := V.toScheme.Modules)).mapIso
    (restrictOpenInclusionIso hVU P).symm ≪≫
    restrictDerivedIso k e ≪≫ (DerivedCategory.Q (C := V.toScheme.Modules)).mapIso
      ((restrict k).mapBiprod E C)⟩⟩

lemma actual_affine_attachment_map {U V X : Scheme.{u}} [QuasiSeparatedSpace X]
    [CompactSpace U] [IsAffine V] (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ u : E ⊞ E⟦(1 : ℤ)⟧ ⟶ (restrict j).obj P, QuasiIso u ∧
        ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap u n) := by
  obtain ⟨P, hP, u, hu⟩ := exists_perfect_extension_across_affine_openImmersion j k hcover E hE
  exact ⟨P, hP, u, hu, fun n => by infer_instance⟩

lemma finite_affine_union_without_compact_base {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (E : CochainComplex U.toScheme.Modules ℤ)
    (hE : locallyPerfect U.toScheme E) (s : Finset X.affineOpens) :
    ∃ (hUS : U ≤ U ⊔ s.sup (fun V => V.val))
      (P : CochainComplex (U ⊔ s.sup (fun V => V.val)).toScheme.Modules ℤ),
      locallyPerfect (U ⊔ s.sup (fun V => V.val)).toScheme P ∧
      Nonempty (Retract ((DerivedCategory.Q (C := U.toScheme.Modules)).obj E)
        ((DerivedCategory.Q (C := U.toScheme.Modules)).obj ((restrict (X.homOfLE hUS)).obj P))) :=
  exists_perfect_retract_on_finite_affine_union U hU E hE s

lemma empty_open_arbitrary_original_complex {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace
  X]
    (E : CochainComplex (⊥ : X.Opens).toScheme.Modules ℤ) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex (⊥ : X.Opens).toScheme.Modules ℤ),
      locallyPerfect X P ∧ locallyPerfect (⊥ : X.Opens).toScheme C ∧
      Nonempty ((DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj
        ((restrict (⊥ : X.Opens).ι).obj P) ≅
        (DerivedCategory.Q (C := (⊥ : X.Opens).toScheme.Modules)).obj (E ⊞ C)) := by
  apply locallyPerfect_exists_global_perfect_complement ⊥ (by simp) E
  intro x
  exact False.elim x.property

lemma original_arbitrary_openImmersion {U X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] [CompactSpace U] (j : U ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E) :
    ∃ (P : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ), locallyPerfect X P
      ∧ locallyPerfect U C ∧
      ∃ e : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P) ≅
        (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ C),
        e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ := by
  obtain ⟨P, C, hP, hC, ⟨e⟩⟩ :=
    locallyPerfect_exists_global_perfect_complement_of_openImmersion j E hE
  exact ⟨P, C, hP, hC, e, e.hom_inv_id, e.inv_hom_id⟩

end QuillenTest.GlobalPerfectDensity
