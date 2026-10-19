/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialTransport

/-! Proof-choice independence of the actual whole-track comparison. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ)

/-- Equality transport is independent of the proof of the same whole-track equation. -/
theorem comparisonOfEq_proof_irrel (h' : A = B) :
    comparisonOfEq M A B h X = comparisonOfEq M A B h' X := by
  cases Subsingleton.elim h h'
  rfl

end Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
