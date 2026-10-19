/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentation
public import Quillen.KTheory.Bass.SchemeTrackSequentialProofChoice

/-! Explicit proof-independent comparison formulas for the actual parameter Models. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterTensorPresentation
open GlobalSectionChangeIndex SchemeTrackSequentialPresentation

/-- The fixed direction of the proved ambient whole-track equation. -/
theorem ambientTrack_transport_eq (Q : Scheme.{u}) :
    ParameterLaurentTrack.ambientTrack Q = ParameterTensorNormalizedTrack.ambientTrack Q :=
  (ParameterTensorNormalizedTrack.ambientTrack_eq Q).symm

/-- The fixed direction of the proved supported whole-track equation. -/
theorem supportedTrack_transport_eq {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] :
    ParameterLaurentTrack.supportedTrack f = ParameterTensorNormalizedTrack.supportedTrack f :=
  (ParameterTensorNormalizedTrack.supportedTrack_eq f).symm

/-- The actual ambient comparison uses the proved whole-track equation
independently of its proof. -/
theorem ambientComparison_eq_raw (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    ambientComparison Q X = comparisonOfEq (ParameterModels.ambient Q)
      (ParameterLaurentTrack.ambientTrack Q) (ParameterTensorNormalizedTrack.ambientTrack Q)
      (ambientTrack_transport_eq Q) X := by
  unfold ambientComparison
  apply comparisonOfEq_proof_irrel

/-- The supported comparison retains the same actual whole-track transport. -/
theorem supportedComparison_eq_raw {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    supportedComparison f X = comparisonOfEq (ParameterModels.supported f)
      (ParameterLaurentTrack.supportedTrack f) (ParameterTensorNormalizedTrack.supportedTrack f)
      (supportedTrack_transport_eq f) X := by
  unfold supportedComparison
  apply comparisonOfEq_proof_irrel

end Quillen.PerfectComplexes.ParameterTensorPresentation
