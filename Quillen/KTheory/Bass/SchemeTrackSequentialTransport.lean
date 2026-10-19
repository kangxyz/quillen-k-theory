/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
public import Quillen.KTheory.Bass.SchemeCurrentStageTelescope

/-! Transport the genuine presentation comparison along an equality of entire original tracks. -/
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

/-- Keep the source telescope literal while transporting the whole chosen presentation track. -/
def comparisonOfEq : (SchemeNaturalSeed.currentTelescope A).obj X ⟶ presentation M B X := by
  subst B
  exact comparison M A X

/-- Equality transport of entire tracks preserves the actual stable comparison. -/
theorem comparisonOfEq_stable : IsStableEquivalence (comparisonOfEq M A B h X) := by
  subst B
  exact comparison_stable M A X

end Quillen.KTheory.Bass.SchemeTrackSequentialPresentation
