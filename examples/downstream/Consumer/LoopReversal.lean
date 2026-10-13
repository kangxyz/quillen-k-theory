/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Quillen.Topology.HomotopyGroups.Loop.Reversal

/-! # Independently universed consumers of the actual reversal normalization -/

noncomputable section
open Quillen
open scoped Topology unitInterval
universe u v w

-- Strict naturality lets a client reverse a geometric comparison without
-- supplying any additional compatibility hypothesis on the original map.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    {γ δ : Path x x} (p : Path γ δ) :
    Path (basedLoopMap f hf (loopReversal γ)) (loopReversal (basedLoopMap f hf δ)) := by
  simpa only [basedLoopMap_loopReversal] using
    loopReversalPath (p.map (basedLoopMap f hf).continuous)

-- The sign is proved after the literal original degree shift, including n = 0.
example {X : Type u} [TopologicalSpace X] {x : X} (n : ℕ)
    (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    (loopShiftEquiv (x := x) n).symm
      (homotopyGroupMap loopReversal loopReversal_refl a) *
        (loopShiftEquiv (x := x) n).symm a = 1 := by
  rw [loopShiftEquiv_symm_loopReversal, inv_mul_cancel]

-- An additive abelian label sees negation because the original geometric
-- reversal acts by inversion, with the actual class unchanged underneath.
example {X : Type u} [TopologicalSpace X] {x : X}
    {A : Type w} [AddCommGroup A]
    (label : HomotopyGroup.Pi 1 X x →* Multiplicative A)
    (a : HomotopyGroup.Pi 0 (Path x x) (Path.refl x)) :
    Multiplicative.toAdd (label ((loopShiftEquiv (x := x) 0).symm
      (homotopyGroupMap loopReversal loopReversal_refl a))) =
      -Multiplicative.toAdd (label ((loopShiftEquiv (x := x) 0).symm a)) := by
  rw [loopShiftEquiv_symm_loopReversal, map_inv]
  rfl
