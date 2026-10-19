/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialConnectingSign

/-!
Actual coefficient localization detects the original geometric boundary classes
with their signed stabilization and original evaluation maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u

namespace QuillenTest.CoefficientInitialConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The evaluated intrinsic boundary recovers the unchanged geometric boundary class after negation. -/
theorem neg_evaluated_boundary_eq_original (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientOpenModel f a).waldhausen.K (n + 1)) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ);
    -((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicEvaluationModelMap f a))
      (stableFiberLiftConnecting
      ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
      ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) (n : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
        (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1)
          (Additive.ofMul x))))) =
      originalKStableEquiv (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) n
        (Additive.ofMul (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
          (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n
          (boundedFlatCoefficientOpenKEquiv f a (n + 1) x))) := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  dsimp only
  exact neg_eq_iff_eq_neg.mpr
    (boundedFlatCoefficientInitialConnecting_original_sign f a n κ x)

end QuillenTest.CoefficientInitialConnecting
