/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedRoofs
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.KernelClosure
public import Quillen.Aglib.Algebra.Homology.HomotopyPullback.QuasiIso
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.HomotopyPullback

/-!
# Actual affine chain factorization

The original strict/local perfect factorization retains both literal chain equations, both
degreewise split epimorphisms and the actual strict/local kernels.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- Original affine weak-arrow target factorization. Both downward maps are
split epic in every degree, with actual strict/local-perfect kernels. The
factorization and weak-arrow square commute as literal chain-map equalities. -/
lemma exists_strict_dual_factorization (R : CommRingCat.{u})
    (P : StrictPerfect (Spec R)) (B B' : CochainComplex (Spec R).Modules ℤ)
    (hB' : locallyPerfect (Spec R) B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : StrictPerfect (Spec R)) (D : CochainComplex (Spec R).Modules ℤ)
      (c : C.obj ⟶ P.obj) (d : D ⟶ B) (u : C.obj ⟶ D) (v : B' ⟶ D),
      locallyPerfect (Spec R) D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      strictPerfect (Spec R) (kernel c) ∧ locallyPerfect (Spec R) (kernel d) := by
  obtain ⟨A, M, N, a, p, t, s, q, hM, hN, hp, ht, hs, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    exists_strict_homotopy_roof R P B B' hB' w b
  let C₀ := homotopyPullback a (𝟙 P.obj)
  let cA : C₀ ⟶ A.obj := homotopyPullbackFst a (𝟙 P.obj)
  let c : C₀ ⟶ P.obj := homotopyPullbackSnd a (𝟙 P.obj)
  have hC : strictPerfect (Spec R) C₀ :=
    strictPerfect_homotopyPullback A.property P.property P.property a (𝟙 P.obj)
  have hcA : QuasiIso cA := quasiIso_homotopyPullbackFst a (𝟙 P.obj)
  let D := homotopyPullback q s
  let d : D ⟶ B := homotopyPullbackSnd q s
  have hD : locallyPerfect (Spec R) D := locallyPerfect_homotopyPullback hM
    ((locallyPerfect_iff_of_quasiIso w).mp (locallyPerfect_of_strictPerfect P.property)) hN q s
  have H : Homotopy ((cA ≫ p) ≫ q) ((c ≫ w) ≫ s) := by
    have Hc : Homotopy (cA ≫ a) c := by
      simpa only [Category.comp_id] using homotopyPullbackProjectionHomotopy a (𝟙 P.obj)
    have Hpre : Homotopy ((cA ≫ p) ≫ q) ((cA ≫ a) ≫ w ≫ s) := by
      simpa only [Category.assoc] using H₁.compLeft cA
    have Hpost : Homotopy ((cA ≫ a) ≫ w ≫ s) ((c ≫ w) ≫ s) := by
      simpa only [Category.assoc] using Hc.compRight (w ≫ s)
    exact Hpre.trans Hpost
  let u : C₀ ⟶ D := homotopyPullbackLift q s (cA ≫ p) (c ≫ w) H
  let v : B' ⟶ D := homotopyPullbackLift q s t b H₂
  have hu : QuasiIso u := quasiIso_homotopyPullbackLift q s (cA ≫ p) (c ≫ w) H
  have hv : QuasiIso v := quasiIso_homotopyPullbackLift q s t b H₂
  have hc (i : ℤ) : IsSplitEpi (c.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi a (𝟙 P.obj) i)
  have hd (i : ℤ) : IsSplitEpi (d.f i) :=
    IsSplitEpi.mk' (homotopyPullbackSndSplitEpi q s i)
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  exact ⟨⟨C₀, hC⟩, D, c, d, u, v, hD, hu, hv,
    homotopyPullbackLift_snd q s (cA ≫ p) (c ≫ w) H,
    homotopyPullbackLift_snd q s t b H₂, hc, hd,
    strictPerfect_kernel_of_epi hC P.property c,
    locallyPerfect_kernel_of_epi hD
      ((locallyPerfect_iff_of_quasiIso w).mp (locallyPerfect_of_strictPerfect P.property)) d⟩


end Quillen.PerfectComplexes.Affine

end

end
