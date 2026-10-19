/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryConnectingEvaluation

/-! The original native boundary, after actual fiber conversion, lies in the kernel
of forgetting intersection support. No compactness or comparison assumption is supplied. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace QuillenTest.CoefficientAuxiliaryConnectingEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual support-forget map kills the original native connecting class. -/
theorem native_boundary_forgets_to_one (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K (n + 1)) :
    KMap (boundedFlatCoefficientSupportedFiberForget_exact f T a) n
      ((boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).symm
        (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
          (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
            f T a) n x)) = 1 := by
  let N := boundedFlatCoefficientSupportedOpenNested f T a
  let hN := boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
    f T a
  have hk : (KMap (acyclicInclusion_exact N) n).comp
      (boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).toMonoidHom =
      KMap (boundedFlatCoefficientSupportedFiberForget_exact f T a) n := by
    change (KMap (acyclicInclusion_exact N) n).comp
      (KMap (boundedFlatCoefficientSupportedFiberToAcyclic_exact f T a) n) = _
    rw [KMap_comp_KMap]
  have hb : changeWeakConnectingHom N hN n x ∈
      (changeWeakConnectingHom N hN n).range := ⟨x, rfl⟩
  rw [range_changeWeakConnectingHom_eq_ker_acyclicInclusion] at hb
  have he := DFunLike.congr_fun hk
    ((boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).symm
      (changeWeakConnectingHom N hN n x))
  change KMap (acyclicInclusion_exact N) n
    ((boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n)
      ((boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).symm
        (changeWeakConnectingHom N hN n x))) = _ at he
  rw [MulEquiv.apply_symm_apply] at he
  exact he.symm.trans hb

end QuillenTest.CoefficientAuxiliaryConnectingEvaluation
