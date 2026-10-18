/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterFullFiberComparison

/-! # Both directions of the actual same-null full-open lift comparison -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)

example (h : IsStableEquivalence (currentLift f X)) :
    IsStableEquivalence (twistedLift f X) :=
  (current_twisted_lift_stable_iff f X).mp h

example (h : IsStableEquivalence (twistedLift f X)) :
    IsStableEquivalence (currentLift f X) :=
  (current_twisted_lift_stable_iff f X).mpr h
