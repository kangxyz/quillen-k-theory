/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperation
public import Quillen.Topology.Prespectrum.SelfTrackIntertwining

/-! # Actual intertwining transports original nonnegative K-group operations -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f g : originalPrespectrum W ⟶ originalPrespectrum V}

/-- A supplied whole intertwining identifies the actual homomorphisms on every original K-group. -/
theorem originalKSelfTrackOperation_intertwine
    (H : Homotopy f f) (K : Homotopy g g) (T : Homotopy f g)
    (J : (H.trans T).RelHomotopy (T.trans K)) (n : ℕ) :
    originalKSelfTrackOperation W V H n = originalKSelfTrackOperation W V K n := by
  apply originalKSelfTrackOperation_unique W V K n
  intro a
  rw [originalKSelfTrackOperation_stable, H.stableOperation_intertwine K T J]

end Quillen.Waldhausen.IteratedS
