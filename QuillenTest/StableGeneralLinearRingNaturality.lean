/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.ClassifyingSpace.StableGeneralLinearRingNaturality
public import Mathlib.Data.ZMod.Basic
/-! # The original stable telescope under arbitrary changes of rings -/
open CategoryTheory Quillen Quillen.StableGeneralLinear
open Quillen.StableGeneralLinear.GrothendieckModel
open Quillen.FiniteProjectiveModule.StableCompletion
universe u
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) {X Y : Telescope R}
    (a : X ⟶ Y) :
    ((ringFunctor f).map a).fiber.down = finiteMap f (rank Y.base) a.fiber.down :=
  ringFunctor_map_fiber f a
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ringFunctor f ⋙ projection S = projection R ⋙ smallFunctor (map f) :=
  ringFunctor_projection f
example {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    ((classifyingSpaceMap (ringFunctor f)).hom.comp
      (originalStableToTelescope R)).Homotopic
      ((originalStableToTelescope S).comp
        (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom) :=
  originalStableToTelescope_ringMap f
example :
    ((classifyingSpaceMap (ringFunctor (Int.castRingHom (ZMod 1)))).hom.comp
      (originalStableToTelescope ℤ)).Homotopic
      ((originalStableToTelescope (ZMod 1)).comp
        (classifyingSpaceMap (StableGeneralLinear.map (Int.castRingHom (ZMod 1))).toFunctor).hom) :=
  originalStableToTelescope_ringMap (Int.castRingHom (ZMod 1))
