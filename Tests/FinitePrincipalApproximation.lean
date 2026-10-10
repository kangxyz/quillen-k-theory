/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalApproximation
public import Mathlib.Data.ZMod.Basic

/-! # Original finite-principal approximation consumers

Original localized maps, actual cone exactness, the original derived fiber
square, local single-homology comparisons and projective lifts, the sharp
attachment edge, a proper zero-divisor family, and empty opens are tested.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex Quillen.ModuleComplex.PrincipalLocalization
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
attribute [local instance] HasDerivedCategory.standard
namespace Quillen.Tests.FinitePrincipalApproximation

lemma original_localized_free_map_surjective {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) (s : Finset R)
    (hfinite : ∀ r : s, Module.Finite (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val))) :
    ∃ (m : ℕ) (g : ModuleCat.of R (Fin m → R) ⟶ M), ∀ r : s,
      Function.Surjective ((ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)).map g) := by
  obtain ⟨m, g, hg⟩ := exists_finiteFree_epi_on_principals M s hfinite
  exact ⟨m, g, fun r => (ModuleCat.epi_iff_surjective _).mp (hg r)⟩

lemma original_localized_cone_exact (R : CommRingCat.{u}) (K : ModuleComplex R)
    (n : ℤ) (s : Finset R)
    (hb : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) n)
    (hf : ∀ r : s, Module.Finite (Localization.Away r.val)
      (((localize r.val (.up ℤ)).obj K).homology n)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K), ∀ r : s, ∀ i : ℤ, n-1 < i →
        ((localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)).ExactAt i := by
  obtain ⟨m, f, h⟩ := exists_finiteFree_single_lowering_on_principals K n s hb hf
  refine ⟨m, f, fun r i hi => ?_⟩
  have := (h r).2
  exact CochainComplex.exactAt_of_isLE _ (n-1) i hi

/-- The actual derived fiber equation survives the original associated-sheaf
functor, with the genuine global strict source. -/
lemma original_geometric_fiber_square (R : CommRingCat.{u}) {K C : ModuleComplex R}
    (q : K ⟶ C) (hq : (finiteProjectiveDerivedObjects R).trW (DerivedCategory.Q.map q)) :
    ∃ (P : ModuleComplex R) (_ : strictPerfect (Spec R) ((associatedComplex R).obj P))
      (f : P ⟶ K)
      (e : DerivedCategory.Q.obj (CochainComplex.mappingCone f) ≅ DerivedCategory.Q.obj C),
      (associatedDerived R).map (DerivedCategory.Q.map (CochainComplex.mappingCone.inr f)) ≫
        ((associatedDerived R).mapIso e).hom = (associatedDerived R).map (DerivedCategory.Q.map q)
          := by
  obtain ⟨P, hP, f, e, he⟩ := exists_moduleStrictPerfect_fiber_of_perfect_cone R q hq
  refine ⟨P, strictPerfect_associated R hP, f, e, ?_⟩
  simpa using congrArg (associatedDerived R).map he

section Models
variable (R : CommRingCat.{u}) (K : ModuleComplex R) (a b : ℤ) (s : Finset R)
    (hb : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b)
    (hm : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P))

include hb hm in
lemma original_local_remainder_all_homology :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K), ∀ r : s,
      let C := (localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)
      ∃ g : (CochainComplex.singleFunctor (ModuleCat.{u} (Localization.Away r.val)) a).obj
          (C.homology a) ⟶ C,
        (∀ i, IsIso (homologyMap g i)) ∧
        (singleObjHomologySelfIso (.up ℤ) a (C.homology a)).inv ≫ homologyMap g a = 𝟙 _ := by
  obtain ⟨P, hP, f, h⟩ :=
    exists_moduleStrictPerfect_approximation_with_local_projective_remainder R K a b s hb hm
  refine ⟨P, hP, f, fun r => ?_⟩
  obtain ⟨_, _, _, _, g, hg, he⟩ := h r
  exact ⟨g, fun i => inferInstance, he⟩

include hb hm in
lemma actual_local_remainder_projective_lifts :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K), ∀ r : s,
      let C := (localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)
      ∀ (A B : ModuleCat.{u} (Localization.Away r.val)) (p : A ⟶ B) (_ : Epi p)
        (g : C.homology a ⟶ B), ∃ l : C.homology a ⟶ A, l ≫ p = g := by
  obtain ⟨P, hP, f, h⟩ :=
    exists_moduleStrictPerfect_approximation_with_local_projective_remainder R K a b s hb hm
  refine ⟨P, hP, f, fun r A B p hp g => ?_⟩
  have := (h r).2.2.2.1
  exact ⟨Projective.factorThru g p, Projective.factorThru_comp g p⟩
end Models

lemma attachment_lower_edge (R : CommRingCat.{u}) (K : ModuleComplex R) (a : ℤ)
    (s : Finset R)
    (hb : ∀ r : s, CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) (a+1))
    (hm : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ (m : ℕ) (f : (CochainComplex.singleFunctor (ModuleCat.{u} R) (a+1)).obj
      (ModuleCat.of R (Fin m → R)) ⟶ K), ∀ r : s,
        CochainComplex.IsLE ((localize r.val (.up ℤ)).obj (CochainComplex.mappingCone f)) a := by
  obtain ⟨m, f, hf, _⟩ := exists_finiteFree_single_lowering_finite_principal_models
    R K a (a+1) (by omega) s hb hm
  exact ⟨m, f, fun r => by simpa using (hf r).2⟩

/-- Empty families impose no perfection or boundedness condition on the
original ambient module complex, even over a nonzero ring. -/
lemma empty_family_arbitrary_ambient (R : CommRingCat.{u}) (K : ModuleComplex R) (a b : ℤ) :
    ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (_ : P ⟶ K), True := by
  obtain ⟨P, hP, f, _⟩ := exists_moduleStrictPerfect_approximation_with_local_projective_remainder
    R K a b ∅ (fun r => (Finset.notMem_empty _ r.property).elim)
      (fun r => (Finset.notMem_empty _ r.property).elim)
  exact ⟨P, hP, f, trivial⟩

/-- A proper principal family over a ring with zero divisors is enough for
actual local surjectivity; it provably does not span the unit ideal. -/
lemma proper_zero_divisor_family (M : ModuleCat (ZMod 6))
    (hf : ∀ r : ({2, 0} : Finset (ZMod 6)), Module.Finite (Localization.Away r.val)
      (M.localizedModule (Submonoid.powers r.val))) :
    Ideal.span (({2, 0} : Finset (ZMod 6)) : Set (ZMod 6)) ≠ ⊤ ∧
      ∃ (m : ℕ) (g : ModuleCat.of (ZMod 6) (Fin m → ZMod 6) ⟶ M),
        ∀ r : ({2, 0} : Finset (ZMod 6)),
          Function.Surjective ((ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)).map g) :=
            by
  refine ⟨?_, original_localized_free_map_surjective M {2, 0} hf⟩
  simp only [Finset.coe_insert, Finset.coe_singleton, Ideal.span_pair_zero]
  intro h
  have hu : IsUnit (2 : ZMod 6) := Ideal.span_singleton_eq_top.mp h
  exact (by decide : ¬ Nat.Coprime 2 6) ((ZMod.isUnit_iff_coprime 2 6).mp hu)

/-- Localization at zero needs no finite generation of the ambient module. -/
lemma zero_localization_arbitrary_module {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    ∃ (m : ℕ) (g : ModuleCat.of R (Fin m → R) ⟶ M),
      Epi ((ModuleCat.localizedModuleFunctor (Submonoid.powers (0 : R))).map g) := by
  classical
  have : Subsingleton (Localization.Away (0 : R)) :=
    IsLocalization.subsingleton (M := Submonoid.powers (0 : R))
      (S := Localization.Away (0 : R)) ⟨1, by simp⟩
  obtain ⟨m, g, hg⟩ := exists_finiteFree_epi_on_principals M {0} (by
    rintro ⟨r, hr⟩
    have hr : r = 0 := Finset.mem_singleton.mp hr
    subst r
    infer_instance)
  exact ⟨m, g, hg ⟨0, Finset.mem_singleton_self 0⟩⟩

end Quillen.Tests.FinitePrincipalApproximation
