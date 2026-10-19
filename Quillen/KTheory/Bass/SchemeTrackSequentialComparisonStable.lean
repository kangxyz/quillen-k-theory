/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialComparison

/-! Stability of the whole natural comparison, with original source-track transport. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan

/-- Every component of the original-source natural comparison is a stable equivalence. -/
theorem comparisonNatTransOfEq_stable
    (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((comparisonNatTransOfEq M A B h).app X) := by
  rw [comparisonNatTransOfEq_app]
  exact comparisonOfEq_stable M A B h X

end Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
