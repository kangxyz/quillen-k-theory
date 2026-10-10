/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.MayerVietorisForget

/-! # Support-forgetting Mayer–Vietoris consumers -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Tests.SupportedMayerVietorisForget
open Quillen.PerfectComplexes
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hT : IsCompact (T : Set X)) (hZ : IsCompact (Z : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- The full unchanged K1→K0 boundary square forgets the prescribed support. -/
theorem original_zero_boundary_square :
    (perfectSupportedKMap Z.ι 0).comp
      (SupportedMayerVietoris.qcqsConnectingHom j T Z hT hZ hcover 0) =
    (PerfectMayerVietoris.qcqsConnectingHom j T hT hcover 0).comp
      (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι 1) :=
  SupportedMayerVietoris.qcqsConnectingHom_forget j T Z hT hZ hcover 0

/-- An actual vanishing supported obstruction also vanishes after support forgetting. -/
theorem forgotten_obstruction_zero (n : ℕ)
    (x : PerfectSupportedK ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1))
    (hx : SupportedMayerVietoris.qcqsConnectingHom j T Z hT hZ hcover n x = 1) :
    PerfectMayerVietoris.qcqsConnectingHom j T hT hcover n
      (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1) x) = 1 := by
  have h := DFunLike.congr_fun
    (SupportedMayerVietoris.qcqsConnectingHom_forget j T Z hT hZ hcover n) x
  simp only [MonoidHom.comp_apply,hx,map_one] at h
  exact h.symm

omit [QuasiSeparatedSpace X] in
/-- Inverse excision compatibility retains the original auxiliary-support inclusion. -/
theorem actual_inverse_fiber_forget (n : ℕ)
    (x : PerfectSupportedK ((j ⁻¹ᵁ Z) ⊔ (j ⁻¹ᵁ T).ι.opensRange).ι n) :
    perfectSupportedUnionForgetKMap T.ι Z n ((SupportedMayerVietoris.fiberEquiv j T Z hcover n).symm
      x) =
      (perfectSupportedExcisionKEquiv j T hcover n).symm
        (perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n x) :=
  DFunLike.congr_fun (SupportedMayerVietoris.fiberEquiv_symm_forget j T Z hcover n) x

end Tests.SupportedMayerVietorisForget
