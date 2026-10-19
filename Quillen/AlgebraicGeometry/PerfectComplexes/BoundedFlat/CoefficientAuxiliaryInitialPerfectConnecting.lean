/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialSupportedConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedOpenNaturality

/-!
# Initial localization and the original perfect boundary

The original bounded-flat inclusion compares actual geometric boundaries. Together
with actual supported evaluation, it identifies the initial intrinsic coefficient
boundary with the negative of the original perfect relative-open boundary. Only
ambient compactness is needed for this comparison.
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

variable [CompactSpace Q.left]

/-- The unchanged original perfect relative-open boundary has the same negative stable sign. -/
theorem boundedFlatCoefficientAuxiliaryInitialConnecting_perfect_sign (a : Under R) (n : ℕ)
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
      -(auxiliaryFiberPerfectStableEquiv f T a n
        (Additive.ofMul (perfectSupportedOpenConnectingHom (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) n
          (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1) x)))) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
  dsimp only
  let y := (boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientFiberSupportOpen f T a).ι n).symm
    (boundedFlatPerfectSupportedOpenConnectingHom (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) n
      (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x))
  have he : auxiliaryFiberPerfectKEquiv f T a n y =
      perfectSupportedOpenConnectingHom (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1) x) := by
    change boundedFlatPerfectSupportedToPerfectSupportedKMap
      (boundedFlatCoefficientFiberSupportOpen f T a).ι n
      (boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientFiberSupportOpen f T a).ι n
        ((boundedFlatCoefficientSupportedSectionKEquiv
        (boundedFlatCoefficientFiberSupportOpen f T a).ι n).symm _)) =
      perfectSupportedOpenConnectingHom (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatPerfectSupportedOpenToPerfectSupportedOpenKMap (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) (n + 1)
          (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x))
    rw [MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun
      (boundedFlatPerfectSupportedOpenConnectingHom_comparison (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) n)
      (boundedFlatCoefficientSupportedOpenKEquiv f T a (n + 1) x)
  have hk := auxiliaryFiberPerfectStableEquiv_evaluation f T a n y
  rw [he] at hk
  exact (boundedFlatCoefficientAuxiliaryInitialConnecting_supported_sign f T a n κ x).trans
    (congrArg Neg.neg hk.symm)

end Quillen.PerfectComplexes
