/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Closure
public import Quillen.Aglib.Algebra.Homology.DerivedCategory.EqualityDenominators
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.HomotopyPullback
public import Quillen.Aglib.Algebra.Homology.HomotopyPullback.QuasiIso
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.KernelClosure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Closure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# Supported chain roofs and strict factorization

Under the original supported derived-roof hypothesis, genuine weak cospans, common denominators and two actual homotopy pullbacks preserve both literal chain triangles, degreewise split epimorphisms and original supported kernels.
-/
@[expose] public section

open Quillen.CochainComplex


open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original supported image witness gives a genuine weak cospan;
both the global model and new local target retain the specified support. -/
lemma exists_weak_cospan {E : CochainComplex U.Modules ℤ} (hE : complexObjects j T E) :
    ∃ (P : CochainComplex X.Modules ℤ) (M : CochainComplex U.Modules ℤ) (p : (restrict j).obj P ⟶ M)
      (s : E ⟶ M),
      perfectSupported T.ι P ∧ perfectSupported (j ⁻¹ᵁ T).ι M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  obtain ⟨M, p, s, hDenIso2, hFac2⟩ := DerivedCategory.left_fac e.hom
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso2
  have he : (e.hom) ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map p := by
    let := hDenIso2
    rw [hFac2, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hp : IsIso ((DerivedCategory.Q (C := U.Modules)).map p) := by rw [← he]; infer_instance
  have hE' := perfectSupported_of_mem j T ⟨P, hP, ⟨e⟩⟩
  exact ⟨P, M, p, s, hP,
    ⟨(locallyPerfect_iff_of_quasiIso s).mp hE'.1,
      (restrictAcyclic_iff_of_quasiIso (j ⁻¹ᵁ T).ι s).mp hE'.2⟩,
    (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules p).mp hp, hs⟩

/-- Genuine module/geometric roofs between global models give a complete
original homotopy roof for arbitrary sheaf-complex targets. The remaining
all-sheaf denominators are legitimate localization denominators only. -/
theorem exists_homotopy_roof (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    (P : CochainComplex X.Modules ℤ) (hP : perfectSupported T.ι P)
      (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j T B') (w : (restrict j).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (A : CochainComplex X.Modules ℤ) (M N : CochainComplex U.Modules ℤ)
      (a : A ⟶ P) (p : (restrict j).obj A ⟶ M) (t : B' ⟶ M)
      (s : B ⟶ N) (q : M ⟶ N),
      perfectSupported T.ι A ∧ perfectSupported (j ⁻¹ᵁ T).ι M ∧ perfectSupported (j ⁻¹ᵁ T).ι N ∧
      QuasiIso p ∧ QuasiIso t ∧ QuasiIso s ∧
      Nonempty (Homotopy (p ≫ q) ((restrict j).map a ≫ w ≫ s)) ∧
      Nonempty (Homotopy (t ≫ q) (b ≫ s)) := by
  obtain ⟨A₀, M, p₀, t, hA₀, hM, hp₀, ht⟩ := exists_weak_cospan j T hB'
  let D := DerivedCategory.Q (C := U.Modules)
  let β : D.obj M ⟶ D.obj B := inv (D.map t) ≫ D.map b
  let α : D.obj ((restrict j).obj A₀) ⟶ D.obj ((restrict j).obj P) :=
    D.map p₀ ≫ β ≫ inv (D.map w)
  obtain ⟨A, r, a, hA, hr, ha, hzA⟩ := hroof A₀ P hA₀.1 hP.1
    ((isZero_toDerived_iff_acyclic _).mpr hA₀.2)
    ((isZero_toDerived_iff_acyclic _).mpr hP.2) α
  have hA' : perfectSupported T.ι A := ⟨hA, (isZero_toDerived_iff_acyclic _).mp hzA⟩
  let p := (restrict j).map r ≫ p₀
  have hp : QuasiIso p := inferInstance
  obtain ⟨N, q, s, hDenIso1, hFac1⟩ := DerivedCategory.left_fac β
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have he : (β) ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map q := by
    let := hDenIso1
    rw [hFac1, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hB : perfectSupported (j ⁻¹ᵁ T).ι B :=
    ⟨(locallyPerfect_iff_of_quasiIso w).mp (locallyPerfect_restrict j hP.1),
      (restrictAcyclic_iff_of_quasiIso (j ⁻¹ᵁ T).ι w).mp
        (perfectSupported_restrict j T hP).2⟩
  have hN : perfectSupported (j ⁻¹ᵁ T).ι N :=
    ⟨(locallyPerfect_iff_of_quasiIso s).mp hB.1,
      (restrictAcyclic_iff_of_quasiIso (j ⁻¹ᵁ T).ι s).mp hB.2⟩
  change D.map ((restrict j).map r) ≫ α = D.map ((restrict j).map a) at ha
  change β ≫ D.map s = D.map q at he
  have heq₁ : D.map (p ≫ q) = D.map ((restrict j).map a ≫ w ≫ s) := by
    simp only [Functor.map_comp]
    rw [← ha, ← he]
    simp [p, α, Category.assoc]
  have heq₂ : D.map (t ≫ q) = D.map (b ≫ s) := by
    rw [Functor.map_comp, ← he]
    simp [β]
  obtain ⟨N', z, hz, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    Quillen.CochainComplex.exists_post_quasiIso_two_homotopies_of_derived_eq
      (C := U.Modules) (p ≫ q) ((restrict j).map a ≫ w ≫ s)
      (t ≫ q) (b ≫ s) heq₁ heq₂
  exact ⟨A, M, N', a, p, t, s ≫ z, q ≫ z, hA', hM,
    ⟨(locallyPerfect_iff_of_quasiIso z).mp hN.1,
      (restrictAcyclic_iff_of_quasiIso (j ⁻¹ᵁ T).ι z).mp hN.2⟩, hp, ht, inferInstance,
    ⟨by simpa only [Category.assoc] using H₁⟩,
    ⟨by simpa only [Category.assoc] using H₂⟩⟩

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Original dual App2 data with both literal triangles, actual componentwise
split epis and genuine kernel membership in the corresponding source/target.
The input roof property concerns only globally perfect models. -/
theorem exists_dual_factorization (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    (P : CochainComplex X.Modules ℤ) (hP : perfectSupported T.ι P)
      (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j T B') (w : (restrict j).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex X.Modules ℤ) (D : CochainComplex U.Modules ℤ)
      (c : C ⟶ P) (d : D ⟶ B) (u : (restrict j).obj C ⟶ D) (v : B' ⟶ D),
      perfectSupported T.ι C ∧ complexObjects j T D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = (restrict j).map c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      perfectSupported T.ι (kernel c) ∧ complexObjects j T (kernel d) := by
  obtain ⟨A, M, N, a, p, t, s, q, hA, hM, hN, hp, ht, hs, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    exists_homotopy_roof j T hroof P hP B B' hB' w b
  let C := homotopyPullback a (𝟙 P)
  let cA : C ⟶ A := homotopyPullbackFst a (𝟙 P)
  let c : C ⟶ P := homotopyPullbackSnd a (𝟙 P)
  have hcA : QuasiIso cA := quasiIso_homotopyPullbackFst a (𝟙 P)
  have hC : perfectSupported T.ι C :=
    ⟨locallyPerfect_homotopyPullback hA.1 hP.1 hP.1 a (𝟙 P),
      (restrictAcyclic_iff_of_quasiIso T.ι cA).mpr hA.2⟩
  let D := homotopyPullback q s
  let d : D ⟶ B := homotopyPullbackSnd q s
  have Hc : Homotopy ((restrict j).map cA ≫ (restrict j).map a) ((restrict j).map c) := by
    simpa only [restrict, cA, c, C, Functor.map_comp, Functor.map_id, Category.comp_id] using
      (Scheme.Modules.restrictFunctor j).mapHomotopy (homotopyPullbackProjectionHomotopy a (𝟙 P))
  have H : Homotopy (((restrict j).map cA ≫ p) ≫ q) (((restrict j).map c ≫ w) ≫ s) := by
    have Hpre : Homotopy (((restrict j).map cA ≫ p) ≫ q)
        (((restrict j).map cA ≫ (restrict j).map a) ≫ w ≫ s) := by
      simpa only [Category.assoc] using H₁.compLeft ((restrict j).map cA)
    have Hpost : Homotopy (((restrict j).map cA ≫ (restrict j).map a) ≫ w ≫ s)
        (((restrict j).map c ≫ w) ≫ s) := by
      simpa only [Category.assoc] using Hc.compRight (w ≫ s)
    exact Hpre.trans Hpost
  let u : (restrict j).obj C ⟶ D := homotopyPullbackLift q s
    ((restrict j).map cA ≫ p) ((restrict j).map c ≫ w) H
  let v : B' ⟶ D := homotopyPullbackLift q s t b H₂
  have hu : QuasiIso u := quasiIso_homotopyPullbackLift q s
    ((restrict j).map cA ≫ p) ((restrict j).map c ≫ w) H
  have hv : QuasiIso v := quasiIso_homotopyPullbackLift q s t b H₂
  have hD : complexObjects j T D := ⟨C, hC, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map u)⟩⟩
  have hB : complexObjects j T B := ⟨P, hP, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map w)⟩⟩
  have hc (i : ℤ) : IsSplitEpi (c.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi a (𝟙 P) i)
  have hd (i : ℤ) : IsSplitEpi (d.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi q s i)
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  let S := ShortComplex.mk (kernel.ι d) d (kernel.condition d)
  have hS : S.ShortExact := {
    exact := S.exact_of_f_is_kernel (kernelIsKernel d)
    mono_f := inferInstance
    epi_g := inferInstance }
  exact ⟨C, D, c, d, u, v, hC, hD, hu, hv,
    homotopyPullbackLift_snd q s ((restrict j).map cA ≫ p) ((restrict j).map c ≫ w) H,
    homotopyPullbackLift_snd q s t b H₂, hc, hd,
    perfectSupported_kernel_of_epi T.ι hC hP c,
    complexObjects_kernel_of_shortExact j T hroof hS hD hB⟩

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end


end
