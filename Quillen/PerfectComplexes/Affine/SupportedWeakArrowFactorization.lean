/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.SupportedOppositeJointData
import Quillen.PerfectComplexes.Affine.WeakArrowFactorization

/-!
# Genuine supported affine weak-arrow factorization

For an arbitrary open immersion into `Spec R`, the actual affine two-pullback
factorization stays in the original supported categories. Support is transported
through the original global quasi-isomorphisms, and actual restricted kernel
sequences keep both component kernels supported. The displayed factorization
and weak-arrow square remain exact chain-map equalities.
-/

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
    (P : (strictSupported j).FullSubcategory) (B B' : Complex (Spec R))
    (hB' : perfectSupported j B') (w : P.obj ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (C : (strictSupported j).FullSubcategory) (D : Complex (Spec R))
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

/-- Literal target dual App2 factorization in the original supported weak-arrow category. -/
lemma supported_weakArrow_target_dual_factorization (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    (A : Waldhausen.WeakArrow.Obj (perfectSupportedWaldhausen j) (strictSupportedToPerfect j))
    (B' : (perfectSupported j).FullSubcategory)
    (b : B' ⟶ (Waldhausen.WeakArrow.target (perfectSupportedWaldhausen j)
      (strictSupportedToPerfect j)).obj A) :
    ∃ (Y : Waldhausen.WeakArrow.Obj (perfectSupportedWaldhausen j) (strictSupportedToPerfect j))
      (f : Y ⟶ A)
      (v : B' ⟶ (Waldhausen.WeakArrow.target (perfectSupportedWaldhausen j)
        (strictSupportedToPerfect j)).obj Y),
      (perfectSupportedWaldhausen j).weq v ∧
      v ≫ (Waldhausen.WeakArrow.target (perfectSupportedWaldhausen j)
        (strictSupportedToPerfect j)).map f = b ∧
      (∀ i, IsSplitEpi (f.hom.left.hom.f i)) ∧
      (∀ i, IsSplitEpi (f.hom.right.hom.f i)) ∧
      strictSupported j (kernel f.hom.left.hom) ∧
      perfectSupported j (kernel f.hom.right.hom) := by
  have hw : QuasiIso A.obj.hom.hom := A.property
  obtain ⟨C, D, c, d, u, v, hD, hu, hv, hs, he, hc, hd, hkc, hkd⟩ :=
    exists_supported_strict_dual_factorization R j A.obj.left A.obj.right.obj B'.obj B'.property
      A.obj.hom.hom b.hom
  let Y : Waldhausen.WeakArrow.Obj (perfectSupportedWaldhausen j) (strictSupportedToPerfect j) :=
    ⟨⟨C, ⟨D, hD⟩, ObjectProperty.homMk u⟩, hu⟩
  let f : Y ⟶ A := ObjectProperty.homMk
    ⟨ObjectProperty.homMk c, ObjectProperty.homMk d, ObjectProperty.hom_ext _ hs.symm⟩
  exact ⟨Y, f, ObjectProperty.homMk v, hv, ObjectProperty.hom_ext _ he, hc, hd, hkc, hkd⟩

end Quillen.PerfectComplexes.Affine
