/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedDenominators
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# Original derived roofs over a finite principal family

For an actual module chain map whose selected principal localizations are
quasi-isomorphisms, every original derived arrow from a bounded finite-projective
source has an actual finite-projective source denominator and an actual global
chain numerator. Their images satisfy the original derived square. Equality
after that same comparison admits a source denominator as well.

The proofs kill the actual cone or cocone obstruction through the genuine
supported perfect-denominator theorem. Original chain inputs retain actual
homotopies between the prescribed composites. Neither target boundedness nor
a cover of the whole affine base is required. Applying this to an actual
geometric derived-unit comparison is a separate step.
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

/-- A genuine finite-principal local quasi-isomorphism can be inverted on an
original derived arrow from a perfect module complex after a perfect denominator.
The numerator and denominator are actual global chain maps. -/
lemma exists_finite_principal_derived_roof (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map η = DerivedCategory.Q.map q ≫ α ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  have hc (r) (hr : r ∈ s) :
      IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCone η))) := by
    have := hη r hr
    exact isZero_localized_mappingCone_of_isIso R r η
  obtain ⟨P', hP', q, hq, hlocal⟩ := exists_perfect_denominator_annihilating_supported_map R s hP hc
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
  obtain ⟨g, hg⟩ := _root_.CochainComplex.exists_chain_representative_of_isKProjective γ
  exact ⟨P', hP', q, g, by rw [hg]; exact hγ.symm, hlocal⟩

lemma isZero_localized_mappingCocone_of_isIso (R : CommRingCat.{u}) (r : R)
    {B N : ModuleComplex R} (η : B ⟶ N)
    [IsIso (DerivedCategory.Q.map ((localize r (.up ℤ)).map η))] :
    IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj (CochainComplex.mappingCocone η))) := by
  let L := localize r (.up ℤ)
  have h := isZero_localized_mappingCone_of_isIso R r η
  exact ((shiftFunctor _ (-1 : ℤ)).map_isZero h).of_iso
    (DerivedCategory.Q.mapIso ((L.commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone η)) ≪≫
      (DerivedCategory.Q.commShiftIso (-1 : ℤ)).app (L.obj (CochainComplex.mappingCone η)))

/-- Equality after the actual locally weak comparison has a genuine perfect
source denominator, invertible on every selected principal open. -/
lemma exists_finite_principal_derived_equality (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α β : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj B)
    (hαβ : α ≫ DerivedCategory.Q.map η = β ≫ DerivedCategory.Q.map η) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = DerivedCategory.Q.map q ≫ β ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
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
  obtain ⟨P', hP', q, hq, hlocal⟩ :=
    exists_perfect_denominator_annihilating_supported_map R s hP hc γ
  refine ⟨P', hP', q, ?_, hlocal⟩
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, hγ, ← Category.assoc, hq, zero_comp]

/-- An original chain numerator is lifted with a genuine prescribed homotopy
of its two original global composites. -/
lemma exists_finite_principal_chain_roof (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (a : P ⟶ N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      Nonempty (Homotopy (g ≫ η) (q ≫ a)) ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  obtain ⟨P', hP', q, g, hg, hq⟩ :=
    exists_finite_principal_derived_roof R s hP η hη (DerivedCategory.Q.map a)
  have := isKProjective_of_moduleStrictPerfect R hP'
  exact ⟨P', hP', q, g,
    ⟨_root_.CochainComplex.homotopyOfDerivedEqOfIsKProjective (g ≫ η) (q ≫ a)
      (by simpa only [CategoryTheory.Functor.map_comp] using hg)⟩, hq⟩

/-- Equality of original composites gives an actual homotopy after the same
kind of perfect, locally weak source denominator. -/
lemma exists_finite_principal_chain_equality (R : CommRingCat.{u}) (s : Finset R)
    {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P) (η : B ⟶ N)
    (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (f g : P ⟶ B)
    (hfg : DerivedCategory.Q.map (f ≫ η) = DerivedCategory.Q.map (g ≫ η)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      Nonempty (Homotopy (q ≫ f) (q ≫ g)) ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  obtain ⟨P', hP', q, hq, hlocal⟩ := exists_finite_principal_derived_equality R s hP η hη
    (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)
    (by simpa only [CategoryTheory.Functor.map_comp] using hfg)
  have := isKProjective_of_moduleStrictPerfect R hP'
  exact ⟨P', hP', q,
    ⟨_root_.CochainComplex.homotopyOfDerivedEqOfIsKProjective (q ≫ f) (q ≫ g)
      (by simpa only [CategoryTheory.Functor.map_comp] using hq)⟩, hlocal⟩

end Quillen.PerfectComplexes.Affine
