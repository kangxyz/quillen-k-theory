/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.SupportedFactorization


public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOppositeJointData
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.WeakArrowFactorization

/-!
# Genuine supported affine weak-arrow factorization

For an arbitrary open immersion into `Spec R`, the actual affine two-pullback
factorization stays in the original supported categories. Support is transported
through the original global quasi-isomorphisms, and actual restricted kernel
sequences keep both component kernels supported. The displayed factorization
and weak-arrow square remain exact chain-map equalities.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

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
