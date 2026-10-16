/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenQCTargetRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.ImmersionDerivedTarget
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure
/-! # Actual affine attachment over an original lower-bounded QC target

The source denominator retains every compact-open support condition on the
chosen affine model. The output map is a literal global chain map to the
unchanged all-sheaf target. The original local derived morphism is recovered.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

lemma exists_perfect_target_glue_over_lowerBounded_qc_spec
    (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {A : CochainComplex U.Modules ℤ} {B : CochainComplex (Spec R).Modules ℤ}
      {L : CochainComplex X.Modules ℤ}
    (hA : locallyPerfect U A) (hB : locallyPerfect (Spec R) B)
    (n : ℤ) [L.IsGE n] (hLqc : ∀ m, (L.homology m).IsQuasicoherent)
    (e : (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.fst j k)).obj A)
      ≅
      (DerivedCategory.Q (C := (pullback j k).Modules)).obj ((restrict (pullback.snd j k)).obj B))
    (φ : (DerivedCategory.Q (C := U.Modules)).obj A ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.Modules)).obj A ≅ (DerivedCategory.Q (C := U.Modules)).obj
        ((restrict j).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d) = φ ∧
        ∀ (Z : (Spec R).Opens), IsCompact (Z : Set (Spec R)) →
          IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj B)) →
          IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj
            ((restrict Z.ι).obj ((restrict k).obj P))) := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  let Q := DerivedCategory.Q (C := (pullback j k).Modules)
  let c := openSquareRestrictIso b a k j pullback.condition.symm
  let γ := e.inv ≫ restrictDerivedHom a φ ≫ Q.map (c.inv.app L)
  have : ((restrict k).obj L).IsGE n := by
    rw [CochainComplex.isGE_iff]
    intro m hm
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((Scheme.Modules.restrictFunctor k).map_isZero
      ((HomologicalComplex.exactAt_iff_isZero_homology L m).mp
        (L.exactAt_of_isGE n m hm))).of_iso (restrictHomologyIso k L m)
  obtain ⟨B', q, p, hB', hq, hp, hs⟩ :=
    Affine.exists_immersion_roof_to_lowerBounded_quasicoherent_target R b hB n
      (Affine.quasicoherent_homology_restrict k L hLqc) γ
  change Q.map ((restrict b).map q) ≫ γ = Q.map ((restrict b).map p) at hp
  let e' := e ≪≫ (asIso (Q.map ((restrict b).map q))).symm
  have he' : restrictDerivedHom a φ =
      e'.hom ≫ restrictDerivedHom b ((DerivedCategory.Q (C := (Spec R).Modules)).map p) ≫ Q.map
        (c.hom.app L) := by
    rw [restrictDerivedHom_map]
    change _ = (e.hom ≫ inv (Q.map ((restrict b).map q))) ≫ _ ≫ _
    rw [← hp]
    simp only [γ, Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    rw [← Q.map_comp, c.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  obtain ⟨P, hP, u, v, d, hu, hv, he⟩ :=
    OpenHomotopyGluing.exists_perfect_glue_of_derived_target_immersions j k hcover hA hB'
      e' φ ((DerivedCategory.Q (C := (Spec R).Modules)).map p) he'
  refine ⟨P, hP, u, d, hu, ?_⟩
  intro Z hZ hz
  exact (hs Z hZ hz).of_iso (restrictDerivedIso Z.ι v).symm

/-- The original local morphism to any lower-bounded QC-homology target extends
across a Spec chart on the actual stabilized source. -/
lemma exists_stabilized_qc_target_extension_across_spec
    (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {E : CochainComplex U.Modules ℤ} {L : CochainComplex X.Modules ℤ} (hE : locallyPerfect U E)
    (n : ℤ) [L.IsGE n] (hLqc : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (DerivedCategory.Q (C := U.Modules)).obj E ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (u : (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧) ≅
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P)) (d : P ⟶ L),
        u.hom ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d) =
          (DerivedCategory.Q (C := U.Modules)).map (biprod.fst : E ⊞ E⟦(1 : ℤ)⟧ ⟶ E) ≫ φ := by
  let a := pullback.fst j k
  let b := pullback.snd j k
  obtain ⟨B, hB, ⟨eB⟩⟩ := exists_strict_stabilized_extension_into_spec R b
    ((restrict a).obj E) (locallyPerfect_restrict a hE)
  have hA : locallyPerfect U (E ⊞ E⟦(1 : ℤ)⟧) :=
    (abelianExactStructure (CochainComplex U.Modules ℤ)).prop_biprod (locallyPerfect U)
      hE (locallyPerfect_shift hE 1)
  let e := (DerivedCategory.Q (C := (pullback j k).Modules)).mapIso
    (restrictStabilizationIso a E) ≪≫ eB.symm
  obtain ⟨P, hP, u, d, hu, _⟩ := exists_perfect_target_glue_over_lowerBounded_qc_spec
    R j k hcover hA (locallyPerfect_of_strictPerfect hB) n hLqc e
      ((DerivedCategory.Q (C := U.Modules)).map biprod.fst ≫ φ)
  exact ⟨P, hP, u, d, hu⟩

lemma exists_retract_qc_target_extension_across_spec
    (R : CommRingCat.{u}) {U X : Scheme.{u}} [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) (k : Spec R ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {E : CochainComplex U.Modules ℤ} {L : CochainComplex X.Modules ℤ} (hE : locallyPerfect U E)
    (n : ℤ) [L.IsGE n] (hLqc : ∀ m, (L.homology m).IsQuasicoherent)
    (φ : (DerivedCategory.Q (C := U.Modules)).obj E ⟶ (DerivedCategory.Q (C := U.Modules)).obj
      ((restrict j).obj L)) :
    ∃ (P : CochainComplex X.Modules ℤ), locallyPerfect X P ∧
      ∃ (r : Retract ((DerivedCategory.Q (C := U.Modules)).obj E)
        ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P)))
        (d : P ⟶ L), r.i ≫ (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map d) = φ := by
  obtain ⟨P, hP, u, d, hu⟩ :=
    exists_stabilized_qc_target_extension_across_spec R j k hcover hE n hLqc φ
  let Q := DerivedCategory.Q (C := U.Modules)
  let r : Retract (Q.obj E) (Q.obj ((restrict j).obj P)) :=
    { i := Q.map biprod.inl ≫ u.hom
      r := u.inv ≫ Q.map biprod.fst
      retract := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [← Q.map_comp, biprod.inl_fst, Q.map_id] }
  refine ⟨P, hP, r, d, ?_⟩
  change (Q.map biprod.inl ≫ u.hom) ≫ _ = _
  rw [Category.assoc, hu, ← Category.assoc, ← Q.map_comp, biprod.inl_fst,
    Q.map_id, Category.id_comp]

end Quillen.PerfectComplexes
