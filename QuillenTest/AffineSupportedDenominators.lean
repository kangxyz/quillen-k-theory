/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalRoofs
public import Mathlib.Data.ZMod.Basic

/-! Original-map consumers for finite principal supported denominators and roofs. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.Affine Quillen.ModuleComplex.PrincipalLocalization
universe u
attribute [local instance] HasDerivedCategory.standard
namespace QuillenTest.AffineSupportedDenominators

open Quillen

variable (R : CommRingCat.{u}) (s : Finset R)

theorem original_supported_factor {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (C : ModuleComplex R) (_ : moduleStrictPerfect R C) (i : P ⟶ C)
      (γ : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj M),
      DerivedCategory.Q.map i ≫ γ = α ∧
      ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj C)) :=
  exists_perfect_supported_factorization R s hP hM α

theorem original_supported_nullhomotopy {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M))) (f : P ⟶ M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      Nonempty (Homotopy (q ≫ f) 0) ∧ DerivedCategory.Q.map q ≫ DerivedCategory.Q.map f = 0 ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) := by
  obtain ⟨P', hP', q, ⟨H⟩, hq⟩ := exists_perfect_denominator_with_supported_nullhomotopy R s hP hM f
  refine ⟨P', hP', q, ⟨H⟩, ?_, hq⟩
  simpa only [CategoryTheory.Functor.map_comp, DerivedCategory.Q.map_zero] using
    DerivedCategory.Q_map_eq_of_homotopy _ H

theorem actual_localized_homology_maps {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (hM : ∀ r ∈ s, IsZero (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj M)))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = 0 ∧
      ∀ r ∈ s, ∀ n : ℤ, IsIso (homologyMap ((localize r (.up ℤ)).map q) n) := by
  obtain ⟨P', hP', q, hq, hl⟩ := exists_perfect_denominator_annihilating_supported_map R s hP hM α
  refine ⟨P', hP', q, hq, fun r hr n => ?_⟩
  have := hl r hr
  infer_instance

theorem original_derived_square {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (η : B ⟶ N) (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η))
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      DerivedCategory.Q.map g ≫ DerivedCategory.Q.map η = DerivedCategory.Q.map q ≫ α ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) :=
  exists_finite_principal_derived_roof R s hP η hη α

theorem original_localized_chain_square {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (η : B ⟶ N) (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (a : P ⟶ N) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P) (g : P' ⟶ B),
      Nonempty (Homotopy (g ≫ η) (q ≫ a)) ∧
      (∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q)) ∧
      ∀ r : R,
        DerivedCategory.Q.map ((localize r (.up ℤ)).map g) ≫
          DerivedCategory.Q.map ((localize r (.up ℤ)).map η) =
        DerivedCategory.Q.map ((localize r (.up ℤ)).map q) ≫
          DerivedCategory.Q.map ((localize r (.up ℤ)).map a) := by
  obtain ⟨P', hP', q, g, ⟨H⟩, hq⟩ := exists_finite_principal_chain_roof R s hP η hη a
  refine ⟨P', hP', q, g, ⟨H⟩, hq, fun r => ?_⟩
  have h := DerivedCategory.Q_map_eq_of_homotopy _
    ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).mapHomotopy H)
  change DerivedCategory.Q.map ((localize r (.up ℤ)).map (g ≫ η)) =
    DerivedCategory.Q.map ((localize r (.up ℤ)).map (q ≫ a)) at h
  rw [(localize r (.up ℤ)).map_comp, (localize r (.up ℤ)).map_comp,
    DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp] at h
  exact h

theorem original_equality_homotopy {P B N : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (η : B ⟶ N) (hη : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map η)) (f g : P ⟶ B)
    (hfg : DerivedCategory.Q.map (f ≫ η) = DerivedCategory.Q.map (g ≫ η)) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      Nonempty (Homotopy (q ≫ f) (q ≫ g)) ∧
      ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map q) :=
  exists_finite_principal_chain_equality R s hP η hη f g hfg

theorem empty_family_unrestricted_target {P M : ModuleComplex R} (hP : moduleStrictPerfect R P)
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj M) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (q : P' ⟶ P),
      DerivedCategory.Q.map q ≫ α = 0 := by
  obtain ⟨P', hP', q, hq, _⟩ :=
    exists_perfect_denominator_annihilating_supported_map R ∅ hP (by simp) α
  exact ⟨P', hP', q, hq⟩

theorem torsion_and_zero_localization
    {P : ModuleComplex (CommRingCat.of (ZMod 6))}
    (hP : moduleStrictPerfect (CommRingCat.of (ZMod 6)) P) :
    ∃ (P' : ModuleComplex (CommRingCat.of (ZMod 6)))
      (_ : moduleStrictPerfect (CommRingCat.of (ZMod 6)) P') (q : P' ⟶ P),
      Nonempty (Homotopy (q ≫ CochainComplex.mappingCone.inr (𝟙 P)) 0) ∧
      ∀ r ∈ ({2, 3, 0} : Finset (ZMod 6)), QuasiIso ((localize r (.up ℤ)).map q) := by
  apply exists_perfect_denominator_with_supported_nullhomotopy _ _ hP
  intro r _
  exact isZero_localized_mappingCone_of_isIso _ r (𝟙 P)

end QuillenTest.AffineSupportedDenominators
