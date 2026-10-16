/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.AlgebraicGeometry.PerfectComplexes.KernelClosure
public import Quillen.AlgebraicGeometry.PerfectComplexes.HomotopyPullback
public import Quillen.Algebra.Homology.HomotopyPullbackQuasiIso
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Literal dual weak-arrow factorization on the original saturated image

The only geometric input is an actual derived roof between globally perfect
models. All subsequent rectification uses genuine localization denominators
and two literal homotopy pullbacks. Neither ordinary pushforward exactness
nor a strict-source representative into arbitrary sheaf terms is presumed.
-/
@[expose] public section

open Quillen.CochainComplex


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Original dual App2 data with both literal triangles, actual componentwise
split epis and genuine kernel membership in the corresponding source/target.
The input roof property concerns only globally perfect models. -/
theorem exists_dual_factorization (hroof : HasDerivedRoofs j)
    (P : CochainComplex X.Modules ℤ) (hP : locallyPerfect X P) (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j B') (w : (restrict j).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : CochainComplex X.Modules ℤ) (D : CochainComplex U.Modules ℤ)
      (c : C ⟶ P) (d : D ⟶ B) (u : (restrict j).obj C ⟶ D) (v : B' ⟶ D),
      locallyPerfect X C ∧ complexObjects j D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = (restrict j).map c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      locallyPerfect X (kernel c) ∧ complexObjects j (kernel d) := by
  obtain ⟨A, M, N, a, p, t, s, q, hA, hM, hN, hp, ht, hs, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    exists_homotopy_roof j hroof P hP B B' hB' w b
  let C := homotopyPullback a (𝟙 P)
  let cA : C ⟶ A := homotopyPullbackFst a (𝟙 P)
  let c : C ⟶ P := homotopyPullbackSnd a (𝟙 P)
  have hC : locallyPerfect X C := locallyPerfect_homotopyPullback hA hP hP a (𝟙 P)
  have hcA : QuasiIso cA := quasiIso_homotopyPullbackFst a (𝟙 P)
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
  have hD : complexObjects j D := ⟨C, hC, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map u)⟩⟩
  have hB : complexObjects j B := ⟨P, hP, ⟨asIso ((DerivedCategory.Q (C := U.Modules)).map w)⟩⟩
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
    locallyPerfect_kernel_of_epi hC hP c,
    complexObjects_kernel_of_shortExact j hroof hS hD hB⟩

end Quillen.PerfectComplexes.OpenDerivedImage
