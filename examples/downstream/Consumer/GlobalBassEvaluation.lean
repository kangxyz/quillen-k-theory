/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationEquivalence

/-! A client of the actual arbitrary-scheme one-step raw Bass evaluation and original seed. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalBassEvaluation
universe u
namespace Consumer.GlobalBassEvaluation

/-- A client obtains a concrete stable comparison into the original integer-base raw cone loop,
with a homotopy of its actual forward seeds, without supplying a geometric filler. -/
theorem actual_stable_seed_comparison (X : Scheme.{u}) :
    ∃ E : parameterLooping (mappingCone (StrictSquare.comparison (sectionSquare X))) ⟶
        GlobalRawBass.step X,
      IsStableEquivalence E ∧
        Nonempty (Homotopy (strictSeed X ≫ E) (evaluation X ≫ GlobalRawBass.transition X)) :=
  ⟨stepEvaluation X, stepEvaluation_isStableEquivalence X, ⟨seedHomotopy X⟩⟩

end Consumer.GlobalBassEvaluation
