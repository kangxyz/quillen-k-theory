/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.FinitePrincipalApproximation
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# Perfect denominators for maps into supported module complexes

Over an arbitrary commutative ring, a derived map from a bounded
finite-projective module complex into a complex vanishing on a finite principal
family factors through an actual bounded finite-projective complex vanishing
on that family. Successive scalar-power mapping cones give this factorization
using the original principal denominator equations.

Taking an actual finite-projective fiber supplies a source denominator that is
a quasi-isomorphism on every selected principal open and annihilates the
original derived map. For a chain map, the annihilation is witnessed by a
literal chain homotopy. The target is unrestricted and the family need not
cover the affine base. Empty families and zero localizations are allowed.

This is the supported-obstruction input to the morphism and equality extension
route in Stacks Project, Tag 08EC, Lemma 36.13.7.
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

lemma isZero_localized_mappingCone_of_isIso (R : CommRingCat.{u}) (r : R)
    {P K : ModuleComplex R} (f : P ⟶ K)
    [IsIso (DerivedCategory.Q.map ((localize r (.up ℤ)).map f))] :
    IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone f))) := by
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  exact (Triangle.isZero₃_of_isIso₁ _
    (DerivedCategory.mappingCone_triangle_distinguished ((localize r (.up ℤ)).map f))
      (by change IsIso (DerivedCategory.Q.map ((localize r (.up ℤ)).map f)); infer_instance)).of_iso
        (DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F))

lemma isZero_localized_mappingCone_of_isZero (R : CommRingCat.{u}) (r : R)
    {P K : ModuleComplex R} (f : P ⟶ K)
    (hP : IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj P)))
    (hK : IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj K))) :
    IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone f))) := by
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  exact (Triangle.isZero₃_of_isZero₁₂ _
    (DerivedCategory.mappingCone_triangle_distinguished ((localize r (.up ℤ)).map f)) hP hK).of_iso
      (DerivedCategory.Q.mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso f F))

/-- A map from a genuine bounded finite-projective module complex into a target
supported away from a finite principal union factors through a genuine perfect
complex with that same support condition. The principal family need not cover Spec. -/
lemma exists_perfect_supported_factorization (R : CommRingCat.{u})
    (s : Finset R) {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (C : ModuleComplex R) (_ : moduleStrictPerfect R C) (i : P ⟶ C)
      (γ : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj M),
      DerivedCategory.Q.map i ≫ γ = α ∧
      ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P, hP, 𝟙 P, α, by simp, by simp⟩
  | @insert r s hr ih =>
    obtain ⟨C, hC, i, γ, hγ, hs⟩ := ih (fun q hq => hM q (Finset.mem_insert_of_mem hq))
    have := isKProjective_of_moduleStrictPerfect R hC
    obtain ⟨g, hg⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective γ
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
      i ≫ CochainComplex.mappingCone.inr d, γ', ?_, ?_⟩
    · rw [CategoryTheory.Functor.map_comp, Category.assoc, ← hγ', hγ]
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqr | hq
      · subst q
        have : IsIso ((localize r (.up ℤ)).map d) := hn
        exact isZero_localized_mappingCone_of_isIso R r d
      · exact isZero_localized_mappingCone_of_isZero R q d (hs q hq) (hs q hq)

/-- A finite principal support condition supplies a genuine perfect denominator
annihilating the original derived map. Its localizations are actual quasi-isomorphisms. -/
lemma exists_perfect_denominator_annihilating_supported_map (R : CommRingCat.{u})
    (s : Finset R) {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = 0 ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  obtain ⟨C, hC, i, γ, hγ, hs⟩ := exists_perfect_supported_factorization R s hP hM α
  have hi : (finiteProjectiveDerivedObjects R).trW (DerivedCategory.Q.map i) :=
    ObjectProperty.trW.mk (finiteProjectiveDerivedObjects R)
      (DerivedCategory.mappingCone_triangle_distinguished i)
      ⟨CochainComplex.mappingCone i, moduleStrictPerfect_mappingCone R hP hC i, ⟨Iso.refl _⟩⟩
  obtain ⟨P', hP', q, e, he⟩ := exists_moduleStrictPerfect_fiber_of_perfect_cone R i hi
  refine ⟨P', hP', q, ?_, ?_⟩
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

/-- For an original chain map the annihilation is witnessed by an actual homotopy,
while the denominator still is the same actual local quasi-isomorphism. -/
lemma exists_perfect_denominator_with_supported_nullhomotopy (R : CommRingCat.{u})
    (s : Finset R) {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (f : P ⟶ M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      Nonempty (Homotopy (q ≫ f) 0) ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  obtain ⟨P', hP', q, hq, hr⟩ :=
    exists_perfect_denominator_annihilating_supported_map R s hP hM (DerivedCategory.Q.map f)
  have := isKProjective_of_moduleStrictPerfect R hP'
  exact ⟨P', hP', q,
    ⟨_root_.CochainComplex.homotopyOfDerivedEqOfIsKProjective (q ≫ f) 0
      (by simpa only [CategoryTheory.Functor.map_comp, DerivedCategory.Q.map_zero] using hq)⟩, hr⟩

end Quillen.PerfectComplexes.Affine
