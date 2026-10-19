/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEmptySupportedParameterModels

/-! # Empty-open support preserves actual finite stages and parameter spectra -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace QuillenTest.EmptySupportedModels

/-- The actual bottom-support forget map is invertible at every original finite S-stage. -/
theorem bottomForget_stage_isIso (X : Scheme.{u}) (n : ℕ) :
    IsIso ((stages n).map (supportedForget (X := op X) (⊥ : X.Opens).ι)) :=
  ((stages n).mapIso (bottomSupportedModelIso (op X))).isIso_hom

/-- The actual parameter support-forget map is invertible on original prespectra. -/
theorem parameterForget_spectrum_isIso {P Q : Scheme.{u}} [IsEmpty P]
    (f : P ⟶ Q) [IsOpenImmersion f] :
    IsIso (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) :=
  (Functor.isoWhiskerRight (ParameterModels.emptySupportedIso f) prespectrumFunctor).isIso_hom

/-- The specified spectrum inverse cancels the original support-forget map. -/
theorem parameterForget_spectrum_inverse {P Q : Scheme.{u}} [IsEmpty P]
    (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) :
    prespectrumFunctor.map ((ParameterModels.emptySupportedIso f).inv.app X) ≫
        prespectrumFunctor.map ((ParameterModels.forget f).app X) = 𝟙 _ := by
  exact ((Functor.isoWhiskerRight
    (ParameterModels.emptySupportedIso f) prespectrumFunctor).app X).inv_hom_id

end QuillenTest.EmptySupportedModels
