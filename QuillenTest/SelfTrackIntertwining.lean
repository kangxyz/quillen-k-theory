/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackIntertwining

/-! # Original operation transport uses an actual supplied comparison track -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology
universe u
namespace QuillenTest.SelfTrackIntertwining
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
variable (H : Homotopy f f) (K : Homotopy g g) (C : Homotopy f g)
variable (J : (H.trans C).RelHomotopy (C.trans K))
include J

/-- Different original maps are allowed; the given comparison is retained on Pi-one. -/
theorem pi_one_transport (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation n 0 a = K.homotopyClassOperation n 0 a :=
  H.homotopyClassOperation_intertwine K C J n 0 a

/-- The exact same comparison transports the original negative-one stable operation. -/
theorem negative_one_transport : H.stableOperation (-1) = K.stableOperation (-1) :=
  H.stableOperation_intertwine K C J (-1)

end QuillenTest.SelfTrackIntertwining
