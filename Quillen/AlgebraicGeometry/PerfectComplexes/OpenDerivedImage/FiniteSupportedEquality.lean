/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedEquality
public import Quillen.Algebra.Homology.DerivedFinitePreEqualityDenominators
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom

/-! # One actual supported denominator for finite original equalities and homotopies

Targets may have independent cohomological lower bounds. Each original equation
or chain homotopy is retained on a common source-supported global denominator.
The statements concern finite families; no higher coherence is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] Affine.standardDerivedSheaves

/-- Different lower-bounded QC targets share one actual global denominator,
retaining the original source support and every original finite-family equation. -/
lemma exists_source_supported_finite_equalizer {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) {ι : Type v} (s : Finset ι)
    (B : ι → CochainComplex X.Modules ℤ) (b : ι → ℤ) [∀ i, (B i).IsGE (b i)]
    (hB : ∀ i n, ((B i).homology n).IsQuasicoherent)
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (α β : ∀ i, (DerivedCategory.Q (C := X.Modules)).obj A ⟶
      (DerivedCategory.Q (C := X.Modules)).obj (B i))
    (heq : ∀ i ∈ s, restrictDerivedHom j (α i) = restrictDerivedHom j (β i)) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj M)) ∧
      ∀ i ∈ s, (DerivedCategory.Q (C := X.Modules)).map q ≫ α i =
        (DerivedCategory.Q (C := X.Modules)).map q ≫ β i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨A,𝟙 A,hA,?_,hzA,?_⟩
      · rw [CategoryTheory.Functor.map_id]
        infer_instance
      · simp
  | @insert i s hi ih =>
      obtain ⟨M,q,hM,hq,hzM,hs⟩ := ih (fun k hk => heq k (Finset.mem_insert_of_mem hk))
      have hh : restrictDerivedHom j ((DerivedCategory.Q (C := X.Modules)).map q ≫ α i) =
          restrictDerivedHom j ((DerivedCategory.Q (C := X.Modules)).map q ≫ β i) := by
        rw [restrictDerivedHom_comp,restrictDerivedHom_comp,heq i (Finset.mem_insert_self i s)]
      obtain ⟨N,r,hN,hr,hzN,hri⟩ := exists_source_supported_denominator_of_restrictDerivedHom_eq
        j T hT hM (b i) (hB i) hzM _ _ hh
      refine ⟨N,r ≫ q,hN,?_,hzN,?_⟩
      · rw [Functor.map_comp]
        infer_instance
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simpa only [Functor.map_comp,Category.assoc] using hri
        · rw [Functor.map_comp,Category.assoc,hs k hk,Category.assoc]

lemma exists_source_supported_finite_homotopies {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {A : CochainComplex X.Modules ℤ} (hA : locallyPerfect X A) {ι : Type v} (s : Finset ι)
    (B : ι → CochainComplex X.Modules ℤ) (b : ι → ℤ) [∀ i, (B i).IsGE (b i)]
    (hB : ∀ i n, ((B i).homology n).IsQuasicoherent)
    (hzA : IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj A)))
    (f g : ∀ i, A ⟶ B i)
    (heq : ∀ i ∈ s, (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map (f i)) =
      (DerivedCategory.Q (C := U.Modules)).map ((restrict j).map (g i))) :
    ∃ (M : CochainComplex X.Modules ℤ) (q : M ⟶ A), locallyPerfect X M ∧ QuasiIso
      ((restrict j).map q) ∧
      IsZero ((DerivedCategory.Q (C := T.toScheme.Modules)).obj ((restrict T.ι).obj M)) ∧
      ∀ i ∈ s, Nonempty (Homotopy (q ≫ f i) (q ≫ g i)) := by
  obtain ⟨P,q,hP,hq,hzP,hfg⟩ := exists_source_supported_finite_equalizer j T hT hA s B b hB hzA
    (fun i => (DerivedCategory.Q (C := X.Modules)).map (f i))
      (fun i => (DerivedCategory.Q (C := X.Modules)).map (g i))
    (fun i hi => by simpa only [restrictDerivedHom_map] using heq i hi)
  let : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
  have he (i) (hi : i ∈ s) : DerivedCategory.Q.{u+1}.map (q ≫ f i) =
      DerivedCategory.Q.{u+1}.map (q ≫ g i) := by
    simpa only [Functor.map_comp] using hfg i hi
  obtain ⟨M,t,ht,H⟩ := Quillen.CochainComplex.exists_pre_quasiIso_finite_homotopies_of_derived_eq
    s B (fun i => q ≫ f i) (fun i => q ≫ g i) he
  refine ⟨M,t ≫ q,(locallyPerfect_iff_of_quasiIso t).mpr hP,?_,?_,?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · exact hzP.of_iso (asIso ((DerivedCategory.Q (C := T.toScheme.Modules)).map
      ((restrict T.ι).map t)))
  · intro i hi
    obtain ⟨H⟩ := H i hi
    exact ⟨by simpa only [Category.assoc] using H⟩

end Quillen.PerfectComplexes.OpenDerivedImage
