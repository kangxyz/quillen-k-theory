/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullFiberComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullNull
public import Quillen.KTheory.Bass.SchemeIteratedSeedNullComparison
public import Quillen.Topology.Prespectrum.FiberLiftNaturality

/-! # The actual original-to-twisted full-open fiber comparison -/
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

/-- Actual three-object stable comparison transports the original full-open fiber lift. -/
theorem iterated_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (iteratedLift f X) ↔ IsStableEquivalence (twistedLift f X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((iteratedForget f).app X) ((iteratedOpen f).app X)
    ((twistedForget f).app X) ((twistedOpen f).app X)
    ((iteratedNull f).homotopy X) ((twistedNull f).homotopy X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (supportedTrack f)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientTrack Q)).app X)
      ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientTrack P)).app X)
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (supportedTrack f) (ambientTrack Q) _ (forget_equivariant f)))
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (ambientTrack Q) (ambientTrack P) _ (fullMap_equivariant f))).symm
    (fun n r x => SchemeIteratedSeedTelescope.null_square
      (supportedTrack f) (ambientTrack Q) (ambientTrack P) _ _
      (forget_equivariant f) (fullMap_equivariant f)
      (fullNull f) (timeSlice_equivariant f) X n r x)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.supported f) (supportedTrack f) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.ambient Q) (ambientTrack Q) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ParameterModels.ambient P) (ambientTrack P) X)

end Quillen.PerfectComplexes.ParameterFullCurrentNull
