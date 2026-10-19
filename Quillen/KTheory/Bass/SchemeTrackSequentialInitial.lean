/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialTransport

/-! The original initial leg under actual whole-track equality transport. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u w
namespace Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization

/-- The initial current inclusion is the actual first forward arrow of the chosen presentation. -/
theorem comparisonOfEq_initial_leg (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    (A B : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (h : A = B)
    (X : Scheme.{u}ᵒᵖ) :
    Telescope.inclusion (vertex squareFunctor M X) (current M A X) 0 ≫
        comparisonOfEq M A B h X =
      ZigzagSequentialization.initialColimitMap (vertex squareFunctor M X)
        (suspendedVertex squareFunctor M X) (forward M B X) (unit squareFunctor M X) := by
  subst B
  exact initial_leg M A X

end Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
