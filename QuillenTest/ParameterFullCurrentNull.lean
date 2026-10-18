/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullCurrentNull

/-! # Original full-open null values and both comparison squares -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterLaurentTrack
open Quillen.PerfectComplexes.ParameterFullCurrentNull
open SchemeNaturalSeed
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((ParameterModels.supported f ⋙ prespectrumFunctor).obj X).space n) :
    ((fullNull f).homotopy X).level n (r, x) =
      (prespectrumMap ((ParameterModels.openRestriction f).app X)).map n
        (((ParameterModels.supportedOpenNull f).homotopy X).level n (r, x)) := rfl

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (supportedTrack f)).obj X).space n) :
    ((telescopeMap (ambientTrack P)).app X).map n
      (((currentNull f).homotopy X).level n (r, x)) =
      ((normalizedNull f).homotopy X).level n
        (r, ((telescopeMap (supportedTrack f)).app X).map n x) := current_null_square f X n r x

example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((normalizedTelescope (supportedTrack f)).obj X).space n) :
    ((conjugacyTelescopeMap (ambientTrack P)).app X).map n
      (((normalizedNull f).homotopy X).level n (r, x)) =
      ((twistedNull f).homotopy X).level n
        (r, ((conjugacyTelescopeMap (supportedTrack f)).app X).map n x) :=
  twisted_null_square f X n r x
