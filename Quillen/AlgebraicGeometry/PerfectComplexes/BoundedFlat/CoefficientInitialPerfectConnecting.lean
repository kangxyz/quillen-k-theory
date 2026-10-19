/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialSupportedConnecting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedKStableComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ConnectingNaturality

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

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatCoefficientSupportedEvaluation boundedFlatCoefficientSupportedSectionEquivalence

variable [CompactSpace Q.left]

/-- The unchanged original perfect relative-open boundary has the same negative stable sign. -/
theorem boundedFlatCoefficientInitialConnecting_perfect_sign (a : Under R) (n : ℕ)
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
      -(boundedFlatCoefficientSupportedKStableEquiv f a n
        (Additive.ofMul (perfectOpenConnectingHom (schemeMap f a) n
          (boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1) x)))) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  dsimp only
  let y := (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm
    (boundedFlatPerfectOpenConnectingHom (schemeMap f a) n
      (boundedFlatCoefficientOpenKEquiv f a (n + 1) x))
  have he : boundedFlatCoefficientSupportedPerfectKEquiv f a n y =
      perfectOpenConnectingHom (schemeMap f a) n
        (boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1) x) := by
    change boundedFlatPerfectSupportedToPerfectSupportedKMap (schemeMap f a) n
      (boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n
        ((boundedFlatCoefficientSupportedSectionKEquiv (schemeMap f a) n).symm _)) =
      perfectOpenConnectingHom (schemeMap f a) n
        (boundedFlatPerfectOpenToPerfectOpenKMap (schemeMap f a) (n + 1)
          (boundedFlatCoefficientOpenKEquiv f a (n + 1) x))
    rw [MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (boundedFlatPerfectOpenConnectingHom_comparison (schemeMap f a) n)
      (boundedFlatCoefficientOpenKEquiv f a (n + 1) x)
  have hk := boundedFlatCoefficientSupportedKStableEquiv_evaluation f a n y
  rw [he] at hk
  exact (boundedFlatCoefficientInitialConnecting_supported_sign f a n κ x).trans
    (congrArg Neg.neg hk.symm)

end Quillen.PerfectComplexes
