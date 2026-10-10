/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalRoofs

/-! # Genuine denominator roofs preserve the source support

Every additional principal localization where the original source is acyclic
also annihilates the constructed factorization object and source denominator.
This is proved through the actual successive scalar cones and perfect fiber.
No support restriction is imposed on the target of the original derived map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard

/-- The actual supported factorization retains every additional principal acyclicity condition on
  its source. -/
lemma exists_perfect_supported_factorization_preserving_source_support (R : CommRingCat.{u})
    (s : Finset R) {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (C : ModuleComplex R) (_ : moduleStrictPerfect R C) (i : P ⟶ C)
      (γ : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj M),
      DerivedCategory.Q.map i ≫ γ = α ∧
      (∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C))) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P, hP, 𝟙 P, α, by simp, by simp, fun _ h => h⟩
  | @insert r s hr ih =>
    obtain ⟨C, hC, i, γ, hγ, hs, hsource⟩ := ih (fun q hq => hM q (Finset.mem_insert_of_mem hq))
    have := isKProjective_of_moduleStrictPerfect R hC
    obtain ⟨g, hg⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective γ
    have heq : DerivedCategory.Q.map ((localize r (.up ℤ)).map g) =
        DerivedCategory.Q.map ((localize r (.up ℤ)).map (0 : C ⟶ M)) :=
      (hM r (Finset.mem_insert_self _ _)).eq_of_tgt _ _
    obtain ⟨n, hn, hnγ⟩ := exists_principal_derived_module_equality R r hC g 0 heq
    let d : C ⟶ C := r ^ n • 𝟙 C
    have hd : DerivedCategory.Q.map d ≫ γ = 0 := by
      rw [← hg, ← DerivedCategory.Q.map_comp]
      simpa only [d, comp_zero, DerivedCategory.Q.map_zero] using hnγ
    obtain ⟨γ', hγ'⟩ := Triangle.yoneda_exact₂ _
      (DerivedCategory.mappingCone_triangle_distinguished d) γ hd
    change DerivedCategory.Q.obj (CochainComplex.mappingCone d) ⟶ DerivedCategory.Q.obj M at γ'
    change γ = DerivedCategory.Q.map (CochainComplex.mappingCone.inr d) ≫ γ' at hγ'
    refine ⟨CochainComplex.mappingCone d, moduleStrictPerfect_mappingCone R hC hC d,
      i ≫ CochainComplex.mappingCone.inr d, γ', ?_, ?_, ?_⟩
    · rw [CategoryTheory.Functor.map_comp, Category.assoc, ← hγ', hγ]
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqr | hq
      · subst q
        have : IsIso ((localize r (.up ℤ)).map d) := hn
        exact isZero_localized_mappingCone_of_isIso R r d
      · exact isZero_localized_mappingCone_of_isZero R q d (hs q hq) (hs q hq)
    · intro q hq
      exact isZero_localized_mappingCone_of_isZero R q d (hsource q hq) (hsource q hq)

/-- The actual perfect denominator annihilates the original derived map and retains all source
  support. -/
lemma exists_perfect_denominator_preserving_source_support (R : CommRingCat.{u})
    (s : Finset R) {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = 0 ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨C, hC, i, γ, hγ, hs, hsource⟩ :=
    exists_perfect_supported_factorization_preserving_source_support R s hP hM α
  have hi : (finiteProjectiveDerivedObjects R).trW (DerivedCategory.Q.map i) :=
    ObjectProperty.trW.mk (finiteProjectiveDerivedObjects R)
      (DerivedCategory.mappingCone_triangle_distinguished i)
      ⟨CochainComplex.mappingCone i, moduleStrictPerfect_mappingCone R hP hC i, ⟨Iso.refl _⟩⟩
  obtain ⟨P', hP', q, e, he⟩ := exists_moduleStrictPerfect_fiber_of_perfect_cone R i hi
  refine ⟨P', hP', q, ?_, ?_, ?_⟩
  · have hz : DerivedCategory.Q.map q ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr q) = 0
    :=
      comp_distTriang_mor_zero₁₂ _ (DerivedCategory.mappingCone_triangle_distinguished q)
    rw [← hγ, ← he, ← Category.assoc, ← Category.assoc, hz, zero_comp, zero_comp]
  · intro r hr
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    let er : DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone q)) ≅
        DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C) :=
      (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone q)).symm ≪≫
        F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app C
    have hc : IsZero (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((localize r (.up ℤ)).map q))) :=
      (hs r hr).of_iso
        ((DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso q F)).symm
          ≪≫ er)
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
    exact (Triangle.isZero₃_iff_isIso₁ _
      (DerivedCategory.mappingCone_triangle_distinguished ((localize r (.up ℤ)).map q))).mp hc
  · intro r hr
    let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
    let er : DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone q)) ≅
        DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C) :=
      (F.mapDerivedCategoryFactors.app (CochainComplex.mappingCone q)).symm ≪≫
        F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app C
    have hc : IsZero (DerivedCategory.Q.obj
        (CochainComplex.mappingCone ((localize r (.up ℤ)).map q))) :=
      (hsource r hr).of_iso
        ((DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso q F)).symm
          ≪≫ er)
    exact Triangle.isZero₁_of_isZero₂₃ _
      (DerivedCategory.mappingCone_triangle_distinguished ((localize r (.up ℤ)).map q)) hr hc

/-- Both original chain arrows satisfy the derived roof square, with every extra source-support
  condition retained. -/
lemma exists_finite_principal_derived_roof_preserving_source_support (R : CommRingCat.{u}) (s :
  Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map η = DerivedCategory.Q.map q ≫ α ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  have hc (r) (hr : r ∈ s) :
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone η))) := by
    have := hη r hr
    exact isZero_localized_mappingCone_of_isIso R r η
  obtain ⟨P', hP', q, hq, hlocal, hsource⟩ := exists_perfect_denominator_preserving_source_support R
    s hP hc
    (α ≫ DerivedCategory.Q.map (CochainComplex.mappingCone.inr η))
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _
    (DerivedCategory.mappingCone_triangle_distinguished η) (DerivedCategory.Q.map q ≫ α)
    (by
      change (DerivedCategory.Q.map q ≫ α) ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr η) = 0
      simpa only [Category.assoc] using hq)
  change DerivedCategory.Q.obj P' ⟶ DerivedCategory.Q.obj B at γ
  change DerivedCategory.Q.map q ≫ α = γ ≫ DerivedCategory.Q.map η at hγ
  have := isKProjective_of_moduleStrictPerfect R hP'
  obtain ⟨g, hg⟩ := Quillen.CochainComplex.exists_chain_representative_of_isKProjective γ
  exact ⟨P', hP', q, g, by rw [hg]; exact hγ.symm, hlocal, hsource⟩

/-- A genuine locally weak denominator equalizes the original derived maps without enlarging source
  support. -/
lemma exists_finite_principal_derived_equality_preserving_source_support (R : CommRingCat.{u}) (s :
  Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj B)
    (hαβ : α ≫ DerivedCategory.Q.map η = β ≫ DerivedCategory.Q.map η) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = DerivedCategory.Q.map q ≫ β ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  have hδ : (α - β) ≫ DerivedCategory.Q.map η = 0 := by
    rw [Preadditive.sub_comp, hαβ, sub_self]
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _
    (DerivedCategory.mappingCocone_triangle_distinguished η) (α - β) hδ
  change DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj (CochainComplex.mappingCocone η) at γ
  change α - β = γ ≫ DerivedCategory.Q.map (CochainComplex.mappingCocone.fst η) at hγ
  have hc (r) (hr : r ∈ s) :
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCocone η))) :=
        by
    have := hη r hr
    exact isZero_localized_mappingCocone_of_isIso R r η
  obtain ⟨P', hP', q, hq, hlocal, hsource⟩ :=
    exists_perfect_denominator_preserving_source_support R s hP hc γ
  refine ⟨P', hP', q, ?_, hlocal, hsource⟩
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, hγ, ← Category.assoc, hq, zero_comp]

/-- Original chain inputs retain an actual global numerator homotopy and all principal source
  support. -/
lemma exists_finite_principal_chain_roof_preserving_source_support (R : CommRingCat.{u}) (s : Finset
  R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (a : P ⟶ N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      Nonempty (Homotopy (g ≫ η) (q ≫ a)) ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r : R, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)) →
        IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P')) := by
  obtain ⟨P', hP', q, g, hg, hq, hsource⟩ :=
    exists_finite_principal_derived_roof_preserving_source_support R s hP η hη
      (DerivedCategory.Q.map a)
  have := isKProjective_of_moduleStrictPerfect R hP'
  exact ⟨P', hP', q, g,
    ⟨Quillen.CochainComplex.homotopyOfDerivedEqOfIsKProjective (g ≫ η) (q ≫ a)
      (by simpa only [CategoryTheory.Functor.map_comp] using hg)⟩, hq, hsource⟩

end Quillen.PerfectComplexes.Affine
