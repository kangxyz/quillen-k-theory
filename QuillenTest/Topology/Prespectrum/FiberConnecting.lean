/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Quillen.Topology.Prespectrum.FiberConnectingStageZero

/-!
# Regression checks for stabilization of the fiber boundary

Two original stabilization steps cancel the coordinate sign. At the smallest nonnegative degree,
the level-one representative instead has exactly the single minus. Neither check assumes Omega.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.FiberConnecting

/-- Two successive original stabilization steps commute with the levelwise boundary. -/
theorem two_structure_steps {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (l k : ℕ)
    (a : HomotopyGroup.Pi (k + 2) (F.space l) (F.point l)) :
    HomotopyFiber.connectingHom (f.map (l + 2)) (F.point (l + 2)) (E.point (l + 2))
        (f.map_point (l + 2)) (k + 2)
        (structurePiMap F (l + 1) (k + 2) (structurePiMap F l (k + 1) a)) =
      structurePiMap (homotopyFiber f) (l + 1) (k + 1)
        (structurePiMap (homotopyFiber f) l k
          (HomotopyFiber.connectingHom (f.map l) (F.point l) (E.point l)
            (f.map_point l) k a)) := by
  rw [connectingHom_structurePiMap_sign, connectingHom_structurePiMap_sign,
    map_inv, inv_inv]

/-- The first stable boundary on a level-one representative retains its one negative sign. -/
theorem degree_one_to_zero {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (a : HomotopyGroup.Pi 2 (F.space 1) (F.point 1)) :
    stableFiberConnecting f 0
        (nonnegativeStableHomotopyι F 1
          (Additive.ofMul (structurePiMap F 1 1 a))) =
      -(nonnegativeStableHomotopyι (homotopyFiber f) 0
        (Additive.ofMul (structurePiMap (homotopyFiber f) 1 0
          (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
            (E.point 1) (f.map_point 1) 0 a)))) := by
  simpa using stableFiberConnecting_nonnegativeLevelOne f 0 rfl a

end QuillenTest.FiberConnecting
