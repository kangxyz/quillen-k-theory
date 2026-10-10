/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectLocalization
public import Mathlib.Data.ZMod.Basic

/-! # Original principal localization sequence consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
universe u
namespace Tests.PrincipalPerfectLocalization
variable (R : CommRingCat.{u}) (r : R)

/-- The actual relative boundary is retained on every original relative class. -/
theorem original_relative_boundary (n : ℕ)
    (a : PerfectOpenK (Quillen.CoherentScheme.principalOpen R r) (n + 1)) :
    principalPerfectConnectingHom R r n
      (perfectOpenKRestrict (Quillen.CoherentScheme.principalOpen R r) (n + 1) a) =
    perfectOpenConnectingHom (Quillen.CoherentScheme.principalOpen R r) n a :=
  DFunLike.congr_fun (principalPerfectConnectingHom_comp_relative R r n) a

/-- A base class vanishing on the original open has an actual supported preimage. -/
theorem actual_supported_preimage (n : ℕ) (x : PerfectK (Spec R) n)
    (hx : perfectKRestrict (Quillen.CoherentScheme.principalOpen R r) n x = 1) :
    ∃ a, perfectSupportedKMap (Quillen.CoherentScheme.principalOpen R r) n a = x := by
  have hm : x ∈ (perfectKRestrict (Quillen.CoherentScheme.principalOpen R r) n).ker := hx
  rw [← range_perfectSupportedKMap_eq_ker_principal_perfectKRestrict] at hm
  exact hm

/-- A supported class dying on the base is the actual boundary of an open class. -/
theorem actual_open_boundary_preimage (n : ℕ)
    (a : PerfectSupportedK (Quillen.CoherentScheme.principalOpen R r) n)
    (ha : perfectSupportedKMap (Quillen.CoherentScheme.principalOpen R r) n a = 1) :
    ∃ x, principalPerfectConnectingHom R r n x = a := by
  have hm : a ∈ (perfectSupportedKMap (Quillen.CoherentScheme.principalOpen R r) n).ker := ha
  rw [← range_principalPerfectConnectingHom_eq_ker_perfectSupportedKMap] at hm
  exact hm

/-- Vanishing of the actual positive boundary gives an original base preimage. -/
theorem actual_base_preimage (n : ℕ)
    (x : PerfectK (Spec (.of (Localization.Away r))) (n + 1))
    (hx : principalPerfectConnectingHom R r n x = 1) :
    ∃ a, perfectKRestrict (Quillen.CoherentScheme.principalOpen R r) (n + 1) a = x := by
  have hm : x ∈ (principalPerfectConnectingHom R r n).ker := hx
  rw [← range_principal_perfectKRestrict_eq_ker_principalPerfectConnectingHom] at hm
  exact hm

/-- The transported boundary is still the actual homotopy-fiber boundary. -/
theorem actual_fiber_boundary (n : ℕ)
    (x : PerfectK (Spec (.of (Localization.Away r))) (n + 1)) :
    perfectSupportedFiberKMap (Quillen.CoherentScheme.principalOpen R r) n
      (principalPerfectConnectingHom R r n x) =
    Quillen.HomotopyFiber.connectingHom
      (Quillen.Waldhausen.Fibration.changeWeakMap
        (perfectOpenNested (Quillen.CoherentScheme.principalOpen R r)))
      (perfectOpenWeakWaldhausen (Quillen.CoherentScheme.principalOpen R r)).kBasepoint
      (perfectWaldhausen (Spec R)).kBasepoint
      (Quillen.Waldhausen.Fibration.changeWeakMap_basepoint
        (perfectOpenNested (Quillen.CoherentScheme.principalOpen R r))) n
      ((principalPerfectOpenKEquiv R r n).symm x) :=
  perfectSupportedFiberKMap_connecting (Quillen.CoherentScheme.principalOpen R r) n _

/-- Localization at zero retains exactness at the original degree-zero base group. -/
theorem zero_localization_K0_exact :
    (perfectSupportedKMap (Quillen.CoherentScheme.principalOpen (.of (ZMod 6)) 0) 0).range =
      (perfectKRestrict (Quillen.CoherentScheme.principalOpen (.of (ZMod 6)) 0) 0).ker :=
  range_perfectSupportedKMap_eq_ker_principal_perfectKRestrict _ _ 0

end Tests.PrincipalPerfectLocalization
