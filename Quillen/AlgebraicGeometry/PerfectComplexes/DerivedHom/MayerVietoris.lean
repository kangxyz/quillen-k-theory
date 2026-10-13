/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.DerivedHomVanishing
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedExtensionByZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.BinaryDescent

/-! # Actual binary-cover derived Hom null-detection with shifted overlap -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
attribute [local instance] HasDerivedCategory.standard
open Quillen.CochainComplex
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
  {K : Complex W} {A : Complex U} {B : Complex V}
  (α : K ⟶ (restrict a).obj A) (β : K ⟶ (restrict b).obj B)

/-- The genuine shifted double adjunction converts overlap Hom vanishing
into null-detection for the original actual glued complex. -/
theorem derivedHom_glued_eq_zero_of_restrictions (L : Complex X)
    (hK : ∀ γ : ((toDerived W).obj K)⟦(1 : ℤ)⟧ ⟶
      (toDerived W).obj ((restrict a).obj ((restrict j).obj L)), γ = 0)
    (φ : (toDerived X).obj (glued a b j k h α β) ⟶ (toDerived X).obj L)
    (hj : restrictDerivedHom j φ = 0) (hk : restrictDerivedHom k φ = 0) : φ = 0 := by
  refine derivedHom_homotopyPushout_eq_zero (left a j α) (right a b j k h β) ?_ φ ?_ ?_
  · intro γ
    apply (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff j ((extensionByZero a).obj K) L 1 γ).mp
    apply (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff a K ((restrict j).obj L) 1 _).mp
    exact hK _
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff j A L _).mp
    rw [extensionByZeroDerivedHomEquiv_postcomp, hj, comp_zero]
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff k B L _).mp
    rw [extensionByZeroDerivedHomEquiv_postcomp, hk, comp_zero]

/-- A full original Hom-vanishing Mayer–Vietoris step. The two local terms are
unshifted, while the actual overlap term is shifted by exactly one. -/
theorem derivedHom_glued_eq_zero (L : Complex X)
    (hA : ∀ γ : (toDerived U).obj A ⟶ (toDerived U).obj ((restrict j).obj L), γ = 0)
    (hB : ∀ γ : (toDerived V).obj B ⟶ (toDerived V).obj ((restrict k).obj L), γ = 0)
    (hK : ∀ γ : ((toDerived W).obj K)⟦(1 : ℤ)⟧ ⟶
      (toDerived W).obj ((restrict a).obj ((restrict j).obj L)), γ = 0)
    (φ : (toDerived X).obj (glued a b j k h α β) ⟶ (toDerived X).obj L) : φ = 0 := by
  refine derivedHom_homotopyPushout_eq_zero (left a j α) (right a b j k h β) ?_ φ ?_ ?_
  · intro γ
    apply (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff j ((extensionByZero a).obj K) L 1 γ).mp
    apply (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff a K ((restrict j).obj L) 1 _).mp
    exact hK _
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff j A L _).mp
    exact hA _
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff k B L _).mp
    exact hB _

end Quillen.PerfectComplexes.OpenHomotopyGluing

namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
open OpenHomotopyGluing
variable {X : Scheme.{u}} (U V : X.Opens) (hUV : U ⊔ V = ⊤)
  (E L : Complex X)

include hUV

/-- Vanishing on an actual binary open cover detects the original derived map
provided the displayed shifted-overlap Hom group is zero. Local nullity alone
is not asserted to suffice. No perfection or finiteness assumptions are needed. -/
theorem derivedHom_eq_zero_of_binaryOpenCover
    (hW : ∀ γ : ((toDerived (pullback U.ι V.ι)).obj
        ((restrict (pullback.fst U.ι V.ι)).obj ((restrict U.ι).obj E)))⟦(1 : ℤ)⟧ ⟶
      (toDerived (pullback U.ι V.ι)).obj
        ((restrict (pullback.fst U.ι V.ι)).obj ((restrict U.ι).obj L)), γ = 0)
    (φ : (toDerived X).obj E ⟶ (toDerived X).obj L)
    (hU : restrictDerivedHom U.ι φ = 0) (hV : restrictDerivedHom V.ι φ = 0) : φ = 0 := by
  let a := pullback.fst U.ι V.ι
  let b := pullback.snd U.ι V.ι
  let e := openSquareRestrictIso b a V.ι U.ι pullback.condition.symm
  let K := (restrict a).obj ((restrict U.ι).obj E)
  let α : K ⟶ (restrict a).obj ((restrict U.ι).obj E) := 𝟙 _
  let β : K ⟶ (restrict b).obj ((restrict V.ι).obj E) := e.inv.app E
  let H : Homotopy (α ≫ (restrict a).map (𝟙 ((restrict U.ι).obj E)))
      (β ≫ (restrict b).map (𝟙 ((restrict V.ι).obj E)) ≫ e.hom.app E) :=
    Homotopy.ofEq (by simp [α, β, K])
  let d := binaryDesc U V α β (𝟙 _) (𝟙 _) H
  have hd : QuasiIso d := quasiIso_binaryDesc U V α β (𝟙 _) (𝟙 _) H hUV
  have hz : (toDerived X).map d ≫ φ = 0 := by
    apply derivedHom_glued_eq_zero_of_restrictions a b U.ι V.ι pullback.condition α β L hW
    · rw [restrictDerivedHom_comp, hU, comp_zero]
    · rw [restrictDerivedHom_comp, hV, comp_zero]
  apply (cancel_epi ((toDerived X).map d)).mp
  simpa only [comp_zero] using hz

end Quillen.PerfectComplexes
