/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterTelescopeNull

/-! # Whole original Spec-row telescope nulls, including the native based-loop level -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.PerfectComplexes
open GlobalSectionChangeIndex GlobalParameterCoefficient
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))

example (s : unitInterval) :
    ((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).at s ≫
        (telescopeIso P).hom.app a =
      (GlobalSupportedParameterCoefficient.telescopeIso f).hom.app a ≫
        ((FullOpenTelescope.null f).homotopy a).at s := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact telescope_fullNull_square f a n s x

example (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj
      (specUnder.obj a)).space 0) :
    ((fineTelescopeComparison P).app a).map 0
      (((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).level 0
        (s, x)) =
      ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level 0
        (s, ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a).map 0 x) :=
  telescope_fullNull_fine_square f a 0 s x

#print axioms fullNull_timeSlice_row
#print axioms finite_fullNull_square
#print axioms telescope_fullNull_square
#print axioms telescope_fullNull_fine_square
