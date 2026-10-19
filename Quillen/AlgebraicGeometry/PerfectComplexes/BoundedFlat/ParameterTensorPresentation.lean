/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorNormalizedTrack
public import Quillen.KTheory.Bass.SchemeTrackSequentialTransport
public import Quillen.KTheory.Bass.SchemeCurrentStageTelescope

/-!
# Actual ordinary-colimit tensor presentations on the localization parameter Models

Ambient and supported objects use their original Model diagrams and actual tensor-normalized
units. The source comparisons are precisely the original current telescopes, using the proved
whole track equalities. The full-open endpoint uses the ambient construction on the open scheme.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterTensorPresentation
open GlobalSectionChangeIndex SchemeNaturalSeed

/-- The actual ordinary pushout colimit for the original ambient parameter Model. -/
def ambient (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  SchemeTrackSequentialPresentation.presentation (ParameterModels.ambient Q)
    (ParameterTensorNormalizedTrack.ambientTrack Q) X

/-- The exact original current ambient telescope maps to the genuine normalized presentation. -/
def ambientComparison (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (currentTelescope (ParameterLaurentTrack.ambientTrack Q)).obj X ⟶ ambient Q X :=
  SchemeTrackSequentialPresentation.comparisonOfEq (ParameterModels.ambient Q)
    (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
    (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm X

/-- The actual ambient comparison is stable without additional localization assumptions. -/
theorem ambientComparison_stable (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ambientComparison Q X) :=
  SchemeTrackSequentialPresentation.comparisonOfEq_stable (ParameterModels.ambient Q)
    (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
    (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm X

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The supported presentation uses the original support full subcategory at every parameter. -/
def supported (X : Scheme.{u}ᵒᵖ) :=
  SchemeTrackSequentialPresentation.presentation (ParameterModels.supported f)
    (ParameterTensorNormalizedTrack.supportedTrack f) X

/-- The exact original supported current telescope maps to the actual supported colimit. -/
def supportedComparison (X : Scheme.{u}ᵒᵖ) :
    (currentTelescope (ParameterLaurentTrack.supportedTrack f)).obj X ⟶ supported f X :=
  SchemeTrackSequentialPresentation.comparisonOfEq (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
    (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm X

/-- Stability uses only actual finite Model topology and the proved whole track identity. -/
theorem supportedComparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (supportedComparison f X) :=
  SchemeTrackSequentialPresentation.comparisonOfEq_stable (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
    (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm X

end Quillen.PerfectComplexes.ParameterTensorPresentation
