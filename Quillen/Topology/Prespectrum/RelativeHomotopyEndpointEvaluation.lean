/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopy

/-! Whole-level evaluation after equality transport of the specified homotopy boundaries. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy

/-- Equality transport of both whole tracks retains every native evaluation coordinate. -/
theorem transport_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K K' : Homotopy f g}
    (p : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) (hH : H = H') (hK : K = K') :
    (p.mp J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst H'
  subst K'
  rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
