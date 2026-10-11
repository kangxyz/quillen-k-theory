/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.Prespectrum.TelescopeHomotopy
import Quillen.Topology.Prespectrum.StableHomotopy

/-! Regression tests for homotopies on actual reduced telescopes. -/

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open Quillen.LoopPrespectrum

universe u

namespace Quillen.Tests.TelescopeHomotopy

variable (E E' : ℕ → LoopPrespectrum.{u})
  (f : ∀ i, E i ⟶ E (i + 1)) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a b : ∀ i, E i ⟶ E' i)
  (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))
  (hb : ∀ i, b i ≫ f' i = f i ≫ b (i + 1))
  (H : ∀ i, Homotopy (a i) (b i))
  (hH : ∀ i k s x, (f' i).map k ((H i).level k (s, x)) =
    (H (i + 1)).level k (s, (f i).map k x))

-- This uses the constructed homotopy to compare induced stable maps, without
-- assuming any formula for the stable groups of the telescope itself.
example (d : ℤ) :
    (stableHomotopyFunctor d).map (Telescope.map E f E' f' a ha) =
      (stableHomotopyFunctor d).map (Telescope.map E f E' f' b hb) :=
  (Telescope.mapHomotopy E f E' f' a b ha hb H hH).stableHomotopyMap_eq d

-- Restricting the telescope homotopy to a stage recovers its original stage
-- homotopy followed by the target stage inclusion, at every time.
example (i : ℕ) (s : unitInterval) :
    Telescope.inclusion E f i ≫ (Telescope.mapHomotopy E f E' f' a b ha hb H hH).at s =
      (H i).at s ≫ Telescope.inclusion E' f' i := by
  apply Hom.ext
  funext k
  ext x
  rfl

-- Constant stage homotopies are compatible using only strict naturality of a.
example : Homotopy (Telescope.map E f E' f' a ha) (Telescope.map E f E' f' a ha) :=
  Telescope.mapHomotopy E f E' f' a a ha ha (fun i ↦ Homotopy.refl (a i))
    (fun i k _s x ↦ congrArg (fun h ↦ h.map k x) (ha i))

end Quillen.Tests.TelescopeHomotopy
