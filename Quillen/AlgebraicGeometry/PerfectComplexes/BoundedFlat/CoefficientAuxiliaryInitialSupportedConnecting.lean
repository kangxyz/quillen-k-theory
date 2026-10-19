/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryNativeClasses
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryConnectingEvaluation

/-!
# The initial intrinsic boundary in the original auxiliary-supported groups

Actual native acyclic conversion is invertible, and its genuine K-equivalence is the
original support conversion followed by actual small-model evaluation. Cancelling this
actual evaluation identifies the initial intrinsic boundary with the negative
of the unchanged supported bounded-flat boundary, in every nonnegative degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- The intrinsic initial boundary retains the original supported bounded-flat boundary and sign. -/
theorem boundedFlatCoefficientAuxiliaryInitialConnecting_supported_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.K (n + 1)) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
          (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1)
            (Additive.ofMul x))) =
      -(modelKStableEquiv (boundedFlatCoefficientSupportedFiberModel f T a) n
        (Additive.ofMul ((boundedFlatCoefficientSupportedSectionKEquiv
          (boundedFlatCoefficientFiberSupportOpen f T a).ι n).symm
          (boundedFlatPerfectSupportedOpenConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a) n
            (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x))))) := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
  dsimp only
  have hi := (ConcreteCategory.isIso_iff_bijective
    ((stableHomotopyFunctor (n : ℤ)).map
      (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a)))).mp
        (auxiliaryNativeFiberAcyclicModelMap_isStableEquivalence f T a (n : ℤ))
  apply hi.injective
  rw [map_neg, auxiliaryNativeFiberAcyclicModelMap_stable]
  have hs := boundedFlatCoefficientAuxiliaryInitialConnecting_native_sign f T a n κ x
  dsimp only at hs
  rw [hs]
  have he := boundedFlatCoefficientSupportedFiberAcyclicKEquiv_symm_connecting f T a n x
  rw [← he]
  have hc := (boundedFlatCoefficientSupportedFiberAcyclicKEquiv f T a n).apply_symm_apply
    (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
      (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a) n x)
  exact congrArg (fun y ↦ -(originalKStableEquiv
    (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) n (Additive.ofMul y)))
      hc.symm

end Quillen.PerfectComplexes
