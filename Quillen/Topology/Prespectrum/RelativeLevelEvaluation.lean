/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! Evaluation of a whole-level relative-homotopy equality with abstract endpoints. -/
@[expose] public section
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
/-- Evaluate the same continuous-map equality before specializing the endpoint data. -/
theorem level_eq_apply {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K') (n : ℕ)
    (e : (J.level n).toContinuousMap = (J'.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    J.level n (r, (s, x)) = J'.level n (r, (s, x)) := DFunLike.congr_fun e _
end Quillen.LoopPrespectrum.Homotopy.RelHomotopy

namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy

theorem ofLevels_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (ofLevels J H' K' hH hK).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl
end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
