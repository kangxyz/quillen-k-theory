/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.UnreducedFirstObstruction

/-! # Detecting a null first obstruction using the literal unreduced cone map -/
@[expose] public section
noncomputable section
open Quillen Quillen.ReducedMappingCone
universe u
namespace Consumer.UnreducedFirstObstruction
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] (f : C(X, Y)) (x : X) (m : ℕ)
  (hf : IsHomotopyConnectedMap f (m + 1))

include hf in
/-- The canonical comparison detects the neutral obstruction, including degree-two obstructions. -/
theorem obstruction_eq_one_iff
    (a : HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :
    piMap m (unreducedFirstObstructionMap f (f x))
      (unreducedFirstObstructionMap_basepoint f x (f x) rfl) a = 1 ↔ a = 1 := by
  constructor
  · intro ha
    apply (unreducedFirstObstructionMap_pi_bijective f x (f x) rfl m hf).injective
    exact ha.trans (map_one _).symm
  · rintro rfl
    exact map_one _

end Consumer.UnreducedFirstObstruction
