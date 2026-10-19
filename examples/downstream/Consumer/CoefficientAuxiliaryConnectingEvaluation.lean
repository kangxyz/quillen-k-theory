/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryConnectingEvaluation

/-! Actual coefficient evaluation detects vanishing of the geometric supported boundary,
including the honest K-zero target, without compactness assumptions. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Consumer.CoefficientAuxiliaryConnectingEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Genuine native evaluation detects the original auxiliary-supported boundary's vanishing. -/
theorem native_boundary_eq_one_iff (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedOpenWaldhausen f T a).K (n + 1)) :
    changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
      (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
        f T a) n x = 1 ↔
      boundedFlatPerfectSupportedOpenConnectingHom (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x) = 1 := by
  rw [← boundedFlatCoefficientSupportedConnecting_evaluation]
  exact (boundedFlatCoefficientSupportedAcyclicSupportKEquiv f T a n).map_eq_one_iff.symm

end Consumer.CoefficientAuxiliaryConnectingEvaluation
