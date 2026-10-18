/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull
public import Quillen.Topology.Prespectrum.FiberLiftNaturality

/-! # Same-null full-open fiber-lift stability across the three actual models -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual current supported inclusion. -/
def currentForget := currentInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual current full-open map. -/
def currentOpen := currentInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the current model. -/
def currentLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((currentOpen f).app X) ((currentForget f).app X)
    ((currentNull f).homotopy X)

/-- The actual normalized supported inclusion. -/
def normalizedForget := normalizedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual normalized full-open map. -/
def normalizedOpen := normalizedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the normalized model. -/
def normalizedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((normalizedOpen f).app X) ((normalizedForget f).app X)
    ((normalizedNull f).homotopy X)

/-- The actual twisted supported inclusion. -/
def twistedForget := twistedInputMap (supportedTrack f) (ambientTrack Q)
  (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (forget_equivariant f)

/-- The actual twisted full-open map. -/
def twistedOpen := twistedInputMap (ambientTrack Q) (ambientTrack P)
  (fullMap f) (fullMap_equivariant f)

/-- The original same-null full-open lift on the twisted model. -/
def twistedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((twistedOpen f).app X) ((twistedForget f).app X)
    ((twistedNull f).homotopy X)

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
theorem current_normalized_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f X) ↔ IsStableEquivalence (normalizedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((currentForget f).app X) ((currentOpen f).app X)
    ((normalizedForget f).app X) ((normalizedOpen f).app X)
    ((currentNull f).homotopy X) ((normalizedNull f).homotopy X)
    ((telescopeMap (supportedTrack f)).app X)
    ((telescopeMap (ambientTrack Q)).app X) ((telescopeMap (ambientTrack P)).app X)
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => current_null_square f X n r x)
    (model_telescopeMap_stable (ParameterModels.supported f) (supportedTrack f) X)
    (model_telescopeMap_stable (ParameterModels.ambient Q) (ambientTrack Q) X)
    (model_telescopeMap_stable (ParameterModels.ambient P) (ambientTrack P) X)

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
theorem normalized_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedLift f X) ↔ IsStableEquivalence (twistedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((normalizedForget f).app X) ((normalizedOpen f).app X)
    ((twistedForget f).app X) ((twistedOpen f).app X)
    ((normalizedNull f).homotopy X) ((twistedNull f).homotopy X)
    ((conjugacyTelescopeMap (supportedTrack f)).app X)
    ((conjugacyTelescopeMap (ambientTrack Q)).app X) ((conjugacyTelescopeMap (ambientTrack
      P)).app X)
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => twisted_null_square f X n r x)
    (model_conjugacyTelescopeMap_stable (ParameterModels.supported f) (supportedTrack f) X)
    (model_conjugacyTelescopeMap_stable (ParameterModels.ambient Q) (ambientTrack Q) X)
    (model_conjugacyTelescopeMap_stable (ParameterModels.ambient P) (ambientTrack P) X)

/-- The two original comparisons give the same-null current/twisted stability equivalence. -/
theorem current_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f X) ↔ IsStableEquivalence (twistedLift f X) :=
  (current_normalized_lift_stable_iff f X).trans (normalized_twisted_lift_stable_iff f X)

end Quillen.PerfectComplexes.ParameterFullCurrentNull
