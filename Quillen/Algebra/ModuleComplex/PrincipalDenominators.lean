/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Principal-open denominators for bounded module complexes

Actual scalar localization clears denominators of chain maps and homotopies
out of finite-support complexes of finitely presented modules over any
commutative ring. No noetherian hypothesis
or asserted geometric replacement property is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ModuleComplex.PrincipalLocalization
variable {R : Type u} [CommRing R]

/-- Actual localization respects scalars through the canonical ring map. -/
theorem localization_map_smul (S : Submonoid R) {M N : ModuleCat.{u} R}
    (a : R) (f : M ⟶ N) :
    (ModuleCat.localizedModuleFunctor S).map (a • f) =
      algebraMap R (Localization S) a • (ModuleCat.localizedModuleFunctor S).map f := by
  apply ModuleCat.hom_ext
  change (IsLocalizedModule.mapExtendScalars S _ _ (Localization S)) (a • f.hom) = _
  rw [map_smul]
  ext x
  exact (IsScalarTower.algebraMap_smul (Localization S) a _).symm

/-- One power clears a module morphism's denominator, preserving that morphism. -/
theorem exists_module_denominator (r : R) (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M]
    (f : M.localizedModule (Submonoid.powers r) ⟶ N.localizedModule (Submonoid.powers r)) :
    ∃ (n : ℕ) (g : M ⟶ N),
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map g = algebraMap R
        (Localization.Away r) (r ^ n) • f := by
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers r)
    (IsLocalizedModule.mapExtendScalars (Submonoid.powers r)
      (M.localizedModuleMkLinearMap _) (N.localizedModuleMkLinearMap _) (Localization.Away r)) f.hom
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, ModuleCat.ofHom g, ModuleCat.hom_ext ?_⟩
  change (IsLocalizedModule.mapExtendScalars _ _ _ _) g = _
  rw [← hs]
  ext x
  simpa [Submonoid.smul_def, ← hn] using
    (IsScalarTower.algebraMap_smul (Localization.Away r) (s : R) (f x)).symm

/-- Equality of localized maps from a finite module is killed by one power. -/
theorem exists_module_power_eq (r : R) (M N : ModuleCat.{u} R)
    [Module.Finite R M] (f g : M ⟶ N)
    (h : (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map f =
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map g) :
    ∃ n : ℕ, r ^ n • f = r ^ n • g := by
  have hc : (N.localizedModuleMkLinearMap (Submonoid.powers r)).comp f.hom =
      (N.localizedModuleMkLinearMap (Submonoid.powers r)).comp g.hom := by
    ext x
    have he := ConcreteCategory.congr_hom h
      (M.localizedModuleMkLinearMap (Submonoid.powers r) x)
    simpa [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap,
      IsLocalizedModule.mapExtendScalars, IsLocalizedModule.map_apply] using he
  obtain ⟨s, hs⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    (Submonoid.powers r) (N.localizedModuleMkLinearMap (Submonoid.powers r)) f.hom g.hom hc
  obtain ⟨n, hn⟩ := s.property
  refine ⟨n, ModuleCat.hom_ext ?_⟩
  simpa [← hn, Submonoid.smul_def] using hs


private theorem exists_uniform_nat {ι : Type*} (s : Finset ι) (P : ι → ℕ → Prop)
    (mono : ∀ i n m, n ≤ m → P i n → P i m)
    (exists_each : ∀ i ∈ s, ∃ n, P i n) : ∃ n, ∀ i ∈ s, P i n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨n, hn⟩ := exists_each i (Finset.mem_insert_self _ _)
    obtain ⟨m, hm⟩ := ih (fun j hj => exists_each j (Finset.mem_insert_of_mem hj))
    refine ⟨max n m, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact mono _ _ _ (le_max_left _ _) hn
    · exact mono _ _ _ (le_max_right _ _) (hm j hj)

/-- A finite-support family of localized module maps has one common power
as denominator. The target family is unrestricted. -/
theorem exists_family_denominator {ι : Type*} (r : R)
    (M N : ι → ModuleCat.{u} R) (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (M i))
    (hfp : ∀ i, Module.FinitePresentation R (M i))
    (f : ∀ i, (M i).localizedModule (Submonoid.powers r) ⟶
      (N i).localizedModule (Submonoid.powers r)) :
    ∃ (n : ℕ) (g : ∀ i, M i ⟶ N i), ∀ i,
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (g i) =
        algebraMap R (Localization.Away r) (r ^ n) • f i := by
  classical
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  let P (i : ι) (n : ℕ) := ∃ g : M i ⟶ N i,
    F.map g = algebraMap R (Localization.Away r) (r ^ n) • f i
  have mono : ∀ i n m, n ≤ m → P i n → P i m := by
    rintro i n m hnm ⟨g, hg⟩
    refine ⟨r ^ (m - n) • g, ?_⟩
    change (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map _ = _
    rw [localization_map_smul, hg, smul_smul, ← map_mul, ← pow_add,
      Nat.sub_add_cancel hnm]
  obtain ⟨n, hn⟩ := exists_uniform_nat s P mono (fun i _ => by
    let := hfp i
    exact exists_module_denominator r (M i) (N i) (f i))
  have hall : ∀ i, P i n := by
    intro i
    by_cases hi : i ∈ s
    · exact hn i hi
    · refine ⟨0, ?_⟩
      exact (F.map_isZero (hz i hi)).eq_of_src _ _
  choose g hg using hall
  exact ⟨n, g, hg⟩

/-- One power makes a finite-support family of maps equal whenever their
actual localizations agree. Only finite generation of the sources is used. -/
theorem exists_family_power_eq {ι : Type*} (r : R)
    (M N : ι → ModuleCat.{u} R) (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (M i)) (hfin : ∀ i, Module.Finite R (M i))
    (f g : ∀ i, M i ⟶ N i)
    (h : ∀ i, (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (f i) =
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (g i)) :
    ∃ n : ℕ, ∀ i, r ^ n • f i = r ^ n • g i := by
  let P (i : ι) (n : ℕ) := r ^ n • f i = r ^ n • g i
  have mono : ∀ i n m, n ≤ m → P i n → P i m := by
    intro i n m hnm hi
    have hm : r ^ m = r ^ (m - n) * r ^ n := by rw [← pow_add, Nat.sub_add_cancel hnm]
    simp only [P, hm, mul_smul, hi]
  obtain ⟨n, hn⟩ := exists_uniform_nat s P mono (fun i _ => by
    let := hfin i
    exact exists_module_power_eq r (M i) (N i) (f i) (g i) (h i))
  exact ⟨n, fun i => by
    by_cases hi : i ∈ s
    · exact hn i hi
    · exact (hz i hi).eq_of_src _ _⟩

/-- Actual scalar localization on complexes. -/
abbrev localize (r : R) {ι : Type*} (c : ComplexShape ι) :=
  (ModuleCat.localizedModuleFunctor.{u} (Submonoid.powers r)).mapHomologicalComplex c

@[simp]
theorem localize_map_smul (r a : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L) :
    (localize r c).map (a • f) =
      algebraMap R (Localization.Away r) a • (localize r c).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact localization_map_smul (Submonoid.powers r) a (f.f i)

/-- Equality on a principal open of chain maps from a finite-support,
degreewise finite complex is witnessed by a single power on the source. -/
theorem exists_chain_power_eq (r : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (K.X i)) (hfin : ∀ i, Module.Finite R (K.X i))
    (f g : K ⟶ L) (h : (localize r c).map f = (localize r c).map g) :
    ∃ n : ℕ, r ^ n • f = r ^ n • g := by
  obtain ⟨n, hn⟩ := exists_family_power_eq r K.X L.X s hz hfin f.f g.f
    (fun i => congrArg (fun e => e.f i) h)
  exact ⟨n, HomologicalComplex.Hom.ext (funext hn)⟩

/-- Every actual localized chain map out of a finite-support complex of
finitely presented modules lifts after multiplying by one power. Both the
source complex and the original localized map are retained. -/
theorem exists_chain_denominator (r : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (K.X i))
    (hfp : ∀ i, Module.FinitePresentation R (K.X i))
    (f : (localize r c).obj K ⟶ (localize r c).obj L) :
    ∃ (n : ℕ) (g : K ⟶ L), (localize r c).map g =
      algebraMap R (Localization.Away r) (r ^ n) • f := by
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r)
  obtain ⟨n, g, hg⟩ := exists_family_denominator r K.X L.X s hz hfp f.f
  change ∀ i, F.map (g i) = algebraMap R (Localization.Away r) (r ^ n) • f.f i at hg
  have hfin (i) : Module.Finite R (K.X i) := by
    let := hfp i
    infer_instance
  have heq (i) : F.map (K.d i (c.next i) ≫ g (c.next i)) =
      F.map (g i ≫ L.d i (c.next i)) := by
    simp only [Functor.map_comp, hg, Linear.comp_smul, Linear.smul_comp]
    exact congrArg (fun t => algebraMap R (Localization.Away r) (r ^ n) • t)
      (f.comm i (c.next i)).symm
  obtain ⟨m, hm⟩ := exists_family_power_eq r K.X (fun i => L.X (c.next i)) s hz hfin
    (fun i => K.d i (c.next i) ≫ g (c.next i))
    (fun i => g i ≫ L.d i (c.next i)) heq
  let G : K ⟶ L :=
    { f := fun i => r ^ m • g i
      comm' := fun i j hij => by
        obtain rfl := c.next_eq' hij
        simpa only [Linear.comp_smul, Linear.smul_comp] using (hm i).symm }
  refine ⟨m + n, G, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext i
  change (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (r ^ m • g i) = _
  rw [localization_map_smul, hg, smul_smul, ← map_mul, ← pow_add]
  rfl


/-- A homotopy between localized chain maps descends after one uniform
power. The descended homotopy localizes to that same power times the
original homotopy, component by component. -/
theorem exists_homotopy_denominator (r : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (K.X i))
    (hfp : ∀ i, Module.FinitePresentation R (K.X i))
    (f g : K ⟶ L) (h : Homotopy ((localize r c).map f) ((localize r c).map g)) :
    ∃ (n : ℕ) (H : Homotopy (r ^ n • f) (r ^ n • g)), ∀ i j,
      (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (H.hom i j) =
        algebraMap R (Localization.Away r) (r ^ n) • h.hom i j := by
  classical
  obtain ⟨n, k, hk⟩ := exists_family_denominator r K.X (fun i => L.X (c.prev i))
    s hz hfp (fun i => h.hom i (c.prev i))
  let H₀ (i j : ι) : K.X i ⟶ L.X j :=
    if hij : c.Rel j i then by
      obtain rfl := c.prev_eq' hij
      exact k i
    else 0
  have H₀zero : ∀ i j, ¬ c.Rel j i → H₀ i j = 0 := by
    intro i j hij
    simp [H₀, hij]
  have H₀map (i j : ι) : (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (H₀ i j) =
      algebraMap R (Localization.Away r) (r ^ n) • h.hom i j := by
    by_cases hij : c.Rel j i
    · obtain rfl := c.prev_eq' hij
      simpa [H₀, hij] using hk i
    · rw [H₀zero i j hij, h.zero i j hij, smul_zero]
      exact (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map_zero _ _
  have heq : (localize r c).map (r ^ n • f) =
      (localize r c).map (Homotopy.nullHomotopicMap H₀ + r ^ n • g) := by
    rw [Functor.map_add, localize_map_smul, localize_map_smul,
      Homotopy.map_nullHomotopicMap]
    apply HomologicalComplex.Hom.ext
    funext i
    have hc := congrArg (fun t => algebraMap R (Localization.Away r) (r ^ n) • t)
      (h.comm i)
    change _ = _ at hc
    simpa only [HomologicalComplex.smul_f_apply, HomologicalComplex.add_f_apply,
      Homotopy.nullHomotopicMap, dNext, prevD, AddMonoidHom.mk'_apply,
      H₀map, smul_add, Linear.comp_smul, Linear.smul_comp] using hc
  have hfin (i) : Module.Finite R (K.X i) := by
    let := hfp i
    infer_instance
  obtain ⟨m, hm⟩ := exists_chain_power_eq r s hz hfin
    (r ^ n • f) (Homotopy.nullHomotopicMap H₀ + r ^ n • g) heq
  let H : Homotopy (r ^ (m + n) • f) (r ^ (m + n) • g) :=
    { hom := fun i j => r ^ m • H₀ i j
      zero := fun i j hij => by rw [H₀zero i j hij, smul_zero]
      comm := fun i => by
        have hc := congrArg (fun e => e.f i) hm
        simpa only [HomologicalComplex.smul_f_apply, HomologicalComplex.add_f_apply,
          Homotopy.nullHomotopicMap, dNext, prevD, AddMonoidHom.mk'_apply,
          pow_add, mul_smul, smul_add, Linear.comp_smul, Linear.smul_comp] using hc }
  refine ⟨m + n, H, fun i j => ?_⟩
  change (ModuleCat.localizedModuleFunctor (Submonoid.powers r)).map (r ^ m • H₀ i j) = _
  rw [localization_map_smul, H₀map, smul_smul, ← map_mul, ← pow_add]

/-- Nullhomotopy after actual localization is killed by a uniform power. -/
theorem exists_nullhomotopy_power (r : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (K.X i))
    (hfp : ∀ i, Module.FinitePresentation R (K.X i))
    (f : K ⟶ L) (h : Homotopy ((localize r c).map f) 0) :
    ∃ n : ℕ, Nonempty (Homotopy (r ^ n • f) 0) := by
  obtain ⟨n, H, _⟩ := exists_homotopy_denominator r s hz hfp f 0
    (by simpa using h)
  exact ⟨n, ⟨by simpa using H⟩⟩


/-- Multiplication by a power becomes an actual chain isomorphism on the
principal open, including when the localization is the zero ring. -/
theorem localize_power_id_isIso (r : R) {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (n : ℕ) :
    IsIso ((localize r c).map (r ^ n • 𝟙 K)) := by
  rw [localize_map_smul, (localize r c).map_id]
  obtain ⟨a, ha⟩ := IsLocalization.map_units (Localization.Away r)
    (⟨r ^ n, n, rfl⟩ : Submonoid.powers r)
  change (a : Localization.Away r) = algebraMap R (Localization.Away r) (r ^ n) at ha
  rw [← ha]
  refine ⟨⟨(↑a⁻¹ : Localization.Away r) • 𝟙 _, ?_, ?_⟩⟩ <;>
    simp [Linear.comp_smul, smul_smul]

/-- Actual principal-open chain-map replacement: a scalar denominator on
the same source becomes an isomorphism, and its composite with the given
localized map is the localization of the constructed numerator. -/
theorem exists_chain_fraction (r : R) {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} R) c} (s : Finset ι)
    (hz : ∀ i ∉ s, IsZero (K.X i))
    (hfp : ∀ i, Module.FinitePresentation R (K.X i))
    (f : (localize r c).obj K ⟶ (localize r c).obj L) :
    ∃ (n : ℕ) (g : K ⟶ L), IsIso ((localize r c).map (r ^ n • 𝟙 K)) ∧
      (localize r c).map (r ^ n • 𝟙 K) ≫ f = (localize r c).map g := by
  obtain ⟨n, g, hg⟩ := exists_chain_denominator r s hz hfp f
  refine ⟨n, g, localize_power_id_isIso r K n, ?_⟩
  rw [localize_map_smul, (localize r c).map_id, Linear.smul_comp, Category.id_comp, hg]

end Quillen.ModuleComplex.PrincipalLocalization
