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

namespace Consumer.CoefficientInitialConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The unchanged geometric boundary detects vanishing before supported evaluation. -/
theorem initial_boundary_eq_zero_iff_original_boundary_eq_one (a : Under R) (n : ℕ)
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
          (Additive.ofMul x))) = 0 ↔
      changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
        (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n
        (boundedFlatCoefficientOpenKEquiv f a (n + 1) x) = 1 := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  dsimp only
  have hi := (ConcreteCategory.isIso_iff_bijective
    ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicEvaluationModelMap f a)))).mp
      (supportAcyclicEvaluationModelMap_stable_isIso f a n)
  have hs := boundedFlatCoefficientInitialConnecting_original_sign f a n κ x
  dsimp only at hs
  constructor
  · intro hx
    rw [hx, map_zero, eq_comm, neg_eq_zero] at hs
    have hz : Additive.ofMul (changeWeakConnectingHom (boundedFlatPerfectOpenNested (schemeMap f a))
        (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n
        (boundedFlatCoefficientOpenKEquiv f a (n + 1) x)) = 0 :=
      (originalKStableEquiv (acyclicStructure (boundedFlatPerfectOpenNested (schemeMap f a))) n).injective (hs.trans (map_zero _).symm)
    exact ofMul_eq_zero.mp hz
  · intro hx
    apply hi.injective
    rw [map_zero]
    rw [hs, hx, ofMul_one, map_zero, neg_zero]

end Consumer.CoefficientInitialConnecting
