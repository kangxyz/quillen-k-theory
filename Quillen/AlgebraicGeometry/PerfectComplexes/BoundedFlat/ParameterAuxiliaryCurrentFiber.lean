/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryTelescopeNull
public import Quillen.Topology.Prespectrum.FiberLiftNaturality

/-! # Same-null auxiliary-supported fiber comparison across the four actual models -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterAuxiliaryCurrentFiber
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The same original auxiliary null gives the actual current fiber lift. -/
def currentLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((currentRestriction f T).app X) ((currentEnlargement f T).app X)
    ((currentNull f T).homotopy X)

/-- The same original auxiliary null gives the actual normalized fiber lift. -/
def normalizedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((normalizedRestriction f T).app X) ((normalizedEnlargement f T).app X)
    ((normalizedNull f T).homotopy X)

/-- The same original auxiliary null gives the actual twisted fiber lift. -/
def twistedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((twistedRestriction f T).app X) ((twistedEnlargement f T).app X)
    ((twistedNull f T).homotopy X)

/-- The same original auxiliary null gives the actual iterated fiber lift. -/
def iteratedLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift ((iteratedRestriction f T).app X) ((iteratedEnlargement f T).app X)
    ((iteratedNull f T).homotopy X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
theorem current_normalized_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (normalizedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    ((normalizedEnlargement f T).app X) ((normalizedRestriction f T).app X)
    ((currentNull f T).homotopy X) ((normalizedNull f T).homotopy X)
    ((telescopeMap (fiberAction f T)).app X)
    ((telescopeMap (ambientAction T)).app X)
    ((telescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (telescopeMap_input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => current_null_square f T X n r x)
    (model_telescopeMap_stable (fiber f T) (fiberAction f T) X)
    (model_telescopeMap_stable (ambient T) (ambientAction T) X)
    (model_telescopeMap_stable (openModel f T) (openAction f T) X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
theorem normalized_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedLift f T X) ↔ IsStableEquivalence (twistedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((normalizedEnlargement f T).app X) ((normalizedRestriction f T).app X)
    ((twistedEnlargement f T).app X) ((twistedRestriction f T).app X)
    ((normalizedNull f T).homotopy X) ((twistedNull f T).homotopy X)
    ((conjugacyTelescopeMap (fiberAction f T)).app X)
    ((conjugacyTelescopeMap (ambientAction T)).app X)
    ((conjugacyTelescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (conjugacyTelescopeMap_input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => twisted_null_square f T X n r x)
    (model_conjugacyTelescopeMap_stable (fiber f T) (fiberAction f T) X)
    (model_conjugacyTelescopeMap_stable (ambient T) (ambientAction T) X)
    (model_conjugacyTelescopeMap_stable (openModel f T) (openAction f T) X)

/-- The actual three stable component maps preserve the original auxiliary fiber lift. -/
theorem iterated_twisted_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (iteratedLift f T X) ↔ IsStableEquivalence (twistedLift f T X) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((iteratedEnlargement f T).app X) ((iteratedRestriction f T).app X)
    ((twistedEnlargement f T).app X) ((twistedRestriction f T).app X)
    ((iteratedNull f T).homotopy X) ((twistedNull f T).homotopy X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (fiberAction f T)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (ambientAction T)).app X)
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (openAction f T)).app X)
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (fiberAction f T) (ambientAction T) _ (enlargement_equivariant f T)))
    (congrArg (fun η => η.app X) (SchemeIteratedSeedTelescope.input_square
      (ambientAction T) (openAction f T) _ (restriction_equivariant f T))).symm
    (fun n r x => iterated_null_square f T X n r x)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (fiber f T) (fiberAction f T) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (ambient T) (ambientAction T) X)
    (SchemeIteratedSeedTelescope.model_iteratedTwistedTelescopeMap_stable
      (openModel f T) (openAction f T) X)

/-- Current-stage and original iterated-seed auxiliary lifts have the same stability property. -/
theorem current_iterated_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (iteratedLift f T X) :=
  (current_normalized_lift_stable_iff f T X).trans
    ((normalized_twisted_lift_stable_iff f T X).trans
      (iterated_twisted_lift_stable_iff f T X).symm)

end Quillen.PerfectComplexes.ParameterAuxiliaryCurrentFiber
