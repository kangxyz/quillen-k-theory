/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassTransitionStable
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentKOperation

/-!
# The original Laurent K-operation in the actual raw Bass transition

The original stable comparison identifies the checked nonnegative K-operation with the same
signed stable operation appearing in the raw transition. The actual parameter-loop shift is
kept explicitly; it contains the alternating stage sign and the original reindexing isomorphism.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual raw transition, after its original signed shift, is the original K-operation
followed by the actual cone inclusion on every nonnegative K-class. -/
theorem boundedFlatCoefficientBassTransition_originalK_shift (n : ℕ)
    (x : BoundedFlatPerfectK (space (op P, a)) n) :
    (parameterStableHomotopyIso
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)).hom
        ((stableHomotopyFunctor (n : ℤ)).map (boundedFlatCoefficientBassTransition P a)
          (originalKStableEquiv (boundedFlatPerfectWaldhausen (space (op P, a))) n
            (Additive.ofMul x))) =
      (stableHomotopyFunctor ((n : ℤ) + 1)).map
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
        (originalKStableEquiv (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj a))) (n + 1)
          (Additive.ofMul (boundedFlatCoefficientLaurentKOperation P a n x))) := by
  have h := ConcreteCategory.congr_hom
    (boundedFlatCoefficientBassTransition_stableHomotopy P a (n : ℤ))
    (originalKStableEquiv (boundedFlatPerfectWaldhausen (space (op P, a))) n
      (Additive.ofMul x))
  change _ = (stableHomotopyFunctor ((n : ℤ) + 1)).map
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
    ((boundedFlatCoefficientLaurentUnitHomotopy P a).stableOperation (n : ℤ)
      (originalKStableEquiv (boundedFlatPerfectWaldhausen (space (op P, a))) n
        (Additive.ofMul x))) at h
  rw [← originalKSelfTrackOperation_stable] at h
  exact h

/-- Solving for the original raw transition keeps the inverse of that same signed shift. -/
theorem boundedFlatCoefficientBassTransition_originalK (n : ℕ)
    (x : BoundedFlatPerfectK (space (op P, a)) n) :
    (stableHomotopyFunctor (n : ℤ)).map (boundedFlatCoefficientBassTransition P a)
      (originalKStableEquiv (boundedFlatPerfectWaldhausen (space (op P, a))) n
        (Additive.ofMul x)) =
      (parameterStableHomotopyIso
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)).inv
        ((stableHomotopyFunctor ((n : ℤ) + 1)).map
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
          (originalKStableEquiv (boundedFlatPerfectWaldhausen
            (space (op P, (laurentUnderFunctor R).obj a))) (n + 1)
            (Additive.ofMul (boundedFlatCoefficientLaurentKOperation P a n x)))) := by
  have h := congrArg
    (parameterStableHomotopyIso
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (n : ℤ)).inv
    (boundedFlatCoefficientBassTransition_originalK_shift P a n x)
  simpa only [← ConcreteCategory.comp_apply, Iso.hom_inv_id,
    ConcreteCategory.id_apply] using h

end Quillen.PerfectComplexes
