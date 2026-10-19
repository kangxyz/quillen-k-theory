/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-! Whole continuous-map recovery for the existing endpoint-level transport of relative tracks. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy

/-- Retyping the two boundary tracks preserves the original whole two-time continuous map. -/
theorem ofLevels_whole_level {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (J.level n).toContinuousMap := rfl

/-- Changing the two endpoint arrows preserves the same entire relative comparison map. -/
theorem cast_whole_level {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} (J : H.RelHomotopy K) (hf : f = f') (hg : g = g') (n : ℕ) :
    ((J.cast hf hg).level n).toContinuousMap = (J.level n).toContinuousMap := rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
