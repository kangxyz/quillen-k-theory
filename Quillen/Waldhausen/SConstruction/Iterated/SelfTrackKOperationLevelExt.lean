/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperation

/-!
# Original K-operations of equal complete self-tracks

Equality of every continuous level first identifies the endpoint maps, then
identifies the original self-track operations. No endpoint cast is discarded.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

/-- Equal complete level tracks induce the same original K-operation. -/
theorem originalKSelfTrackOperation_eq_of_levels
    {f g : originalPrespectrum W ⟶ originalPrespectrum V}
    (H : Homotopy f f) (J : Homotopy g g) (h : ∀ n, H.level n = J.level n) (n : ℕ) :
    originalKSelfTrackOperation W V H n = originalKSelfTrackOperation W V J n := by
  have hf : f = g := by
    apply LoopPrespectrum.Hom.ext
    funext k
    ext x
    exact (H.at_zero k x).symm.trans
      ((congrArg (fun p => p (0, x)) (h k)).trans (J.at_zero k x))
  subst g
  have hH : H = J := by
    apply LoopPrespectrum.Homotopy.ext
    funext k
    exact h k
  subst J
  rfl

end Quillen.Waldhausen.IteratedS
