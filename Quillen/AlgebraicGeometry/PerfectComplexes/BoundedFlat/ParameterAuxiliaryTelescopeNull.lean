/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportNull
public import Quillen.KTheory.Bass.SchemeIteratedSeedNullComparison

/-! # The actual auxiliary-support maps and original null on all four telescopes -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.ParameterLaurentTrack
open SchemeNaturalSeed NaturalTrack
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original forward Laurent action on union-supported objects. -/
abbrev fiberAction := supportedTrack (unionOpen f T).ι

/-- The original forward Laurent action on the ambient auxiliary support. -/
abbrev ambientAction := supportedTrack T.ι

/-- The original forward Laurent action on the inverse-image support. -/
abbrev openAction := supportedTrack (inverseOpen f T).ι

/-- The actual enlargement after the original prespectrum realization. -/
def firstMap := Functor.whiskerRight (enlargement f T) prespectrumFunctor

/-- The actual support restriction after the original prespectrum realization. -/
def secondMap := Functor.whiskerRight (restriction f T) prespectrumFunctor

/-- Every original null slice preserves the same Laurent action. -/
theorem timeSlice_equivariant (r : unitInterval) :
    Equivariant (fiberAction f T) (openAction f T)
      (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
        (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
          (openModel f T ⋙ prespectrumFunctor))
        (fullNull f T).homotopy (fullNull f T).naturality r) := by
  intro X t
  apply Hom.ext
  funext n
  ext x
  exact (fullNull_laurentInterchange f T X n r t x).symm

/-- The actual auxiliary enlargement on the current telescope. -/
def currentEnlargement := currentInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the current telescope. -/
def currentRestriction := currentInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the current telescope. -/
def currentNull := currentInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The actual auxiliary enlargement on the normalized telescope. -/
def normalizedEnlargement := normalizedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the normalized telescope. -/
def normalizedRestriction := normalizedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the normalized telescope. -/
def normalizedNull := normalizedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The actual auxiliary enlargement on the twisted telescope. -/
def twistedEnlargement := twistedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the twisted telescope. -/
def twistedRestriction := twistedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the twisted telescope. -/
def twistedNull := twistedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The actual auxiliary enlargement on the iterated telescope. -/
def iteratedEnlargement := iteratedInputMap (fiberAction f T) (ambientAction T)
  (firstMap f T) (enlargement_equivariant f T)

/-- The actual auxiliary restriction on the iterated telescope. -/
def iteratedRestriction := iteratedInputMap (ambientAction T) (openAction f T)
  (secondMap f T) (restriction_equivariant f T)

/-- Jointly continuous descent of the original auxiliary null to the iterated telescope. -/
def iteratedNull := iteratedInputNull (fiberAction f T) (ambientAction T) (openAction f T)
  (firstMap f T) (secondMap f T) (enlargement_equivariant f T)
  (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T)

/-- The original whole auxiliary null is preserved by the actual current/normalized comparison. -/
theorem current_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (fiberAction f T)).obj X).space n) :
    ((telescopeMap (openAction f T)).app X).map n
      (((currentNull f T).homotopy X).level n (r, x)) =
      ((normalizedNull f T).homotopy X).level n
        (r, ((telescopeMap (fiberAction f T)).app X).map n x) :=
  telescopeMap_null _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x

/-- The original whole auxiliary null is preserved by the actual normalized/twisted comparison. -/
theorem twisted_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (fiberAction f T)).obj X).space n) :
    ((conjugacyTelescopeMap (openAction f T)).app X).map n
      (((normalizedNull f T).homotopy X).level n (r, x)) =
      ((twistedNull f T).homotopy X).level n
        (r, ((conjugacyTelescopeMap (fiberAction f T)).app X).map n x) :=
  conjugacyTelescopeMap_null _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x

/-- The original whole auxiliary null is preserved by the actual iterated/twisted comparison. -/
theorem iterated_null_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((iteratedTelescope (fiberAction f T)).obj X).space n) :
    ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap (openAction f T)).app X).map n
      (((iteratedNull f T).homotopy X).level n (r, x)) =
      ((twistedNull f T).homotopy X).level n
        (r, ((SchemeIteratedSeedTelescope.iteratedTwistedTelescopeMap
          (fiberAction f T)).app X).map n x) :=
  SchemeIteratedSeedTelescope.null_square _ _ _ _ _ (enlargement_equivariant f T)
    (restriction_equivariant f T) (fullNull f T) (timeSlice_equivariant f T) X n r x

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
