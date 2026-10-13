/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.FiberNaturality
public import Quillen.Topology.HomotopyFiber.BasedSquareMap

/-!
# Complete level weak equivalences of the original fiber maps

The existing strict-square fiber map retains its actual source coordinate and entire postcomposed
path. Complete weak equivalences of both original square sides therefore induce complete weak
equivalences of this same fiber map at every specified level, including all path components.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

/-- Weak side maps at the specified level preserve the original full path-space fiber map. -/
theorem homotopyFiberMap_level_isWeakHomotopyEquivalence
    {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B) (n : ℕ)
    (hl : IsWeakHomotopyEquivalence (sq.left.map n))
    (hr : IsWeakHomotopyEquivalence (sq.right.map n)) :
    IsWeakHomotopyEquivalence ((homotopyFiberMap sq).map n) :=
  HomotopyFiber.mapAt_weak (sq.left.map n) (sq.right.map n)
    (by ext x; exact congrArg (fun h ↦ h.map n x) sq.w.symm)
    hl hr (A.right.point n) (B.right.point n) (sq.right.map_point n)

end Quillen.LoopPrespectrum
