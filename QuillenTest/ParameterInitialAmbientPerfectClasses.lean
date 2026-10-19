/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialAmbientPerfectClasses

/-! # The ambient perfect wrapper retains the actual stable evaluation arrow -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace QuillenTest.ParameterInitialAmbientPerfectClasses

/-- Every original perfect representative follows the genuine perfect evaluation map. -/
theorem perfectEvaluation_wrapper {R : CommRingCat.{u}} (i : Index R)
    [CompactSpace i.1.unop.left] (n : ℕ) (x : (perfectWaldhausen (space i)).K n) :
    originalKStableEquiv (perfectWaldhausen (space i)) n (Additive.ofMul x) =
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap i)
        (boundedFlatCoefficientSectionPerfectKStableEquiv i n (Additive.ofMul x)) := by
  obtain ⟨y, rfl⟩ := (boundedFlatCoefficientSectionPerfectKEquiv i n).surjective x
  exact (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap_KEquiv i n y).trans
    (congrArg ((stableHomotopyFunctor (n : ℤ)).map
      (boundedFlatCoefficientSectionPerfectEvaluationPrespectrumMap i))
      (boundedFlatCoefficientSectionPerfectKStableEquiv_evaluation i n y).symm)

end QuillenTest.ParameterInitialAmbientPerfectClasses
