/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5NativeGPhiEntries
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.P5PositiveUnitNative

/-! # The original native G-Phi law

The original weak positive unit completes the negative vanishing and signed
Euler entries. The resulting law retains the original product K-equivalence
and the actual native coefficient and two-summand functors in every degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.ProjectiveLine

namespace Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
open Waldhausen Waldhausen.ExtensionCategory
variable (X : QuasiCompactSchemes.{u})

/-- The positive entry is literally the released original positive model functor. -/
lemma G0First_eq_positive : G0First X = P5NativePositiveUnit.positive X := rfl

/-- The actual original weak unit identifies the first diagonal with the identity. -/
theorem G0First_KMap_eq_id (n : ℕ) :
    KMap (G0First_exact X) n =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen X.obj).K n) :=
  P5NativePositiveUnit.positive_KMap_eq_id X n

/-- Original Euler additivity and the original weak unit give the second diagonal. -/
theorem G1Second_KMap_eq_id (n : ℕ) :
    KMap (G1Second_exact X) n =
      MonoidHom.id ((FlasqueBoundedBelow.waldhausen X.obj).K n) :=
  (G1Second_KMap_eq_G0First X n).trans (G0First_KMap_eq_id X n)

/-- The first original coefficient of Phi is the first original input. -/
theorem G0_Phi_apply_eq_fst (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    KMap (P5NativeCoefficients.G0_exact X) n (P5NativePhi.PhiTwoSummandKMap X n (a, b)) = a := by
  simpa only [G0First_KMap_eq_id, MonoidHom.id_apply] using G0_Phi_apply X n a b

/-- The second original coefficient of Phi is the second original input. -/
theorem G1_Phi_apply_eq_snd (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    KMap (P5NativeCoefficients.G1_exact X) n (P5NativePhi.PhiTwoSummandKMap X n (a, b)) = b := by
  simpa only [G0First_KMap_eq_id, MonoidHom.id_apply] using G1_Phi_apply X n a b

/-- Original G-Phi is the identity in the unchanged original product K-coordinates. -/
theorem GPhiPairKMap_apply_eq_self (n : ℕ)
    (a b : (FlasqueBoundedBelow.waldhausen X.obj).K n) :
    GPhiPairKMap X n (a, b) = (a, b) := by
  simpa only [G0First_KMap_eq_id, MonoidHom.id_apply] using
    GPhiPairKMap_apply_eq_diagonal X n a b

/-- The original pair-coordinate G-Phi homomorphism is the identity in every degree. -/
theorem GPhiPairKMap_eq_id (n : ℕ) :
    GPhiPairKMap X n = MonoidHom.id
      ((FlasqueBoundedBelow.waldhausen X.obj).K n ×
        (FlasqueBoundedBelow.waldhausen X.obj).K n) := by
  apply MonoidHom.ext
  rintro ⟨a, b⟩
  exact GPhiPairKMap_apply_eq_self X n a b

/-- Original G after original Phi fixes the original product-model K group. -/
theorem GPhi_KMap_apply_eq_self (n : ℕ)
    (z : (productStructure (FlasqueBoundedBelow.waldhausen X.obj)
      (FlasqueBoundedBelow.waldhausen X.obj)).K n) :
    KMap (P5NativeCoefficients.G_exact X) n (KMap (P5NativePhi.Phi_exact X) n z) = z := by
  let e := Product.KEquiv (FlasqueBoundedBelow.waldhausen X.obj)
    (FlasqueBoundedBelow.waldhausen X.obj) n
  apply e.injective
  have h : GPhiPairKMap X n (e z) = e z := by
    rcases e z with ⟨a, b⟩
    exact GPhiPairKMap_apply_eq_self X n a b
  change e (KMap (P5NativeCoefficients.G_exact X) n
    (KMap (P5NativePhi.Phi_exact X) n (e.symm (e z)))) = e z at h
  simpa only [MulEquiv.symm_apply_apply] using h

/-- The unconditional original product-model K-map composite G-Phi is the identity. -/
theorem GPhi_KMap_eq_id (n : ℕ) :
    (KMap (P5NativeCoefficients.G_exact X) n).comp (KMap (P5NativePhi.Phi_exact X) n) =
      MonoidHom.id ((productStructure (FlasqueBoundedBelow.waldhausen X.obj)
        (FlasqueBoundedBelow.waldhausen X.obj)).K n) := by
  exact MonoidHom.ext (GPhi_KMap_apply_eq_self X n)

end Quillen.PerfectComplexes.ProjectiveLine.P5NativeEntries
