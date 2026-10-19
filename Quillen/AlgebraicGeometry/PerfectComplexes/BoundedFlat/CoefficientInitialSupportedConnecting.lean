/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialConnectingSign
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportAcyclicKComparison

/-!
# The initial intrinsic boundary in the original supported groups

Actual support evaluation is invertible, and its genuine K-equivalence is the
original section evaluation followed by acyclic conversion. Cancelling this
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

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

/-- The intrinsic initial boundary retains the original supported bounded-flat boundary and sign. -/
theorem boundedFlatCoefficientInitialConnecting_supported_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientOpenModel f a).waldhausen.K (n + 1)) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
          (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1)
            (Additive.ofMul x))) =
      -(modelKStableEquiv (boundedFlatCoefficientSupportedModel f a) n
        (Additive.ofMul ((boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
          (boundedFlatPerfectOpenConnectingHom (schemeMap f a) n
            (boundedFlatCoefficientOpenKEquiv f a (n + 1) x))))) := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  dsimp only
  have hi := (ConcreteCategory.isIso_iff_bijective
    ((stableHomotopyFunctor (n : ℤ)).map
      (prespectrumMap (supportAcyclicEvaluationModelMap f a)))).mp
        (supportAcyclicEvaluationModelMap_stable_isIso f a n)
  apply hi.injective
  rw [map_neg, supportAcyclicEvaluationModelMap_stable]
  have hs := boundedFlatCoefficientInitialConnecting_original_sign f a n κ x
  dsimp only at hs
  rw [hs]
  have he := boundedFlatCoefficientSupportAcyclicEvaluationKEquiv_symm_connecting f a n
    (boundedFlatCoefficientOpenKEquiv f a (n + 1) x)
  rw [← he]
  exact congrArg (fun y ↦ -(originalKStableEquiv
    (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) n (Additive.ofMul y)))
    ((boundedFlatCoefficientEvaluationKEquiv
      (boundedFlatCoefficientSupportedSectionWaldhausen (schemeMap f a))
      (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a)))
      (boundedFlatCoefficientSupportAcyclicEquivalence f a)
      (boundedFlatCoefficientSupportAcyclicEvaluation_exact f a)
      (boundedFlatCoefficientSupportAcyclicEquivalence_inverse_exact f a) n).apply_symm_apply
      (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
        (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n
        (boundedFlatCoefficientOpenKEquiv f a (n + 1) x))).symm

end Quillen.PerfectComplexes
