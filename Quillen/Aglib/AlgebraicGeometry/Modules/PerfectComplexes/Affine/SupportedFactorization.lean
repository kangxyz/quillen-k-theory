/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.Factorization

/-!
# Actual supported affine chain factorization

The same original affine factorization retains the given restricted acyclicity and both actual supported kernels.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- The actual affine factorization retains support through its original
quasi-isomorphisms. Actual restricted short exactness retains both kernels. -/
lemma exists_supported_strict_dual_factorization (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (P : (strictSupported j).FullSubcategory) (B B' : CochainComplex (Spec R).Modules ℤ)
    (hB' : perfectSupported j B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : (strictSupported j).FullSubcategory) (D : CochainComplex (Spec R).Modules ℤ)
      (c : C.obj ⟶ P.obj) (d : D ⟶ B) (u : C.obj ⟶ D) (v : B' ⟶ D),
      perfectSupported j D ∧ QuasiIso u ∧ QuasiIso v ∧
      u ≫ d = c ≫ w ∧ v ≫ d = b ∧
      (∀ i, IsSplitEpi (c.f i)) ∧ (∀ i, IsSplitEpi (d.f i)) ∧
      strictSupported j (kernel c) ∧ perfectSupported j (kernel d) := by
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hs, he, hc, hd, hkc, hkd⟩ :=
    exists_strict_dual_factorization R ⟨P.obj, P.property.1⟩ B B' hB'.1 w b
  have hDs := (restrictAcyclic_iff_of_quasiIso j v).mp hB'.2
  have hCs := (restrictAcyclic_iff_of_quasiIso j u).mpr hDs
  have hBs := (restrictAcyclic_iff_of_quasiIso j w).mp P.property.2
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  exact ⟨⟨C.obj, C.property, hCs⟩, D, c, d, u, v, ⟨hD, hDs⟩, hu, hv, hs, he, hc, hd,
    ⟨hkc, restrictAcyclic_kernel_of_epi j c hCs P.property.2⟩,
    ⟨hkd, restrictAcyclic_kernel_of_epi j d hDs hBs⟩⟩

end Quillen.PerfectComplexes.Affine

end

end
