/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Quillen.Topology.Prespectrum.FiberConnectingLevelOne

/-!
# The original degree-one-to-zero fiber boundary

This independent downstream consumer retains both original level-one stable equivalences and the
single minus introduced by their original stabilization step.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace Consumer.FiberConnecting

/-- The original positive fiber boundary compares with the stable boundary with one minus. -/
theorem original_level_one_boundary {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hF : F.IsOmega) (hFib : (homotopyFiber f).IsOmega)
    (a : HomotopyGroup.Pi 2 (F.space 1) (F.point 1)) :
    stableFiberConnecting f 0 (levelOneStableEquiv F hF 1 (Additive.ofMul a)) =
      -(levelOneStableEquiv (homotopyFiber f) hFib 0
        (Additive.ofMul (HomotopyFiber.connectingHom (f.map 1) (F.point 1)
          (E.point 1) (f.map_point 1) 0 a))) := by
  simpa using stableFiberConnecting_levelOneStableEquiv_sign f hF hFib 0 rfl a

end Consumer.FiberConnecting
