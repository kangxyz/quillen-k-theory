/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.Prespectrum.TelescopeStableMapExt

/-!
# Stable-law consumers for original telescope maps

A strict diagram map and a map made from any supplied transition tracks agree
on the actual signed stable groups. An arbitrary identity track fixes every
original negative stable class, without asserting a point-set identity.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum

namespace Quillen.Tests.TelescopeStableMapExt

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]

/-- Original strict and whole-track maps have the same genuine stable-group homomorphism. -/
theorem strict_map_agrees_with_supplied_tracks
    (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
    (a : ∀ i, E i ⟶ F i) (ha : ∀ i, a i ≫ g i = f i ≫ a (i + 1))
    (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1))) (d : ℤ) :
    (stableHomotopyFunctor d).map (Telescope.map E f F g a ha) =
      (stableHomotopyFunctor d).map (Telescope.mapOfHomotopies E f F g a H) := by
  apply Telescope.stableMap_ext E f
  intro i
  rw [Telescope.inclusion_map, Telescope.inclusion_mapOfHomotopies]

/-- An arbitrary identity track fixes the original class in every negative stable degree. -/
theorem identity_track_fixes_negative_class
    (H : ∀ i, Homotopy (𝟙 (E i) ≫ f i) (f i ≫ 𝟙 (E (i + 1)))) (n : ℕ)
    (x : stableHomotopyGroup (Telescope.prespectrum E f) (-((n : ℤ) + 1))) :
    (stableHomotopyFunctor (-((n : ℤ) + 1))).map
      (Telescope.mapOfHomotopies E f E f (fun i ↦ 𝟙 (E i)) H) x = x :=
  ConcreteCategory.congr_hom (Telescope.stableMap_mapOfHomotopies_id E f H _) x

end Quillen.Tests.TelescopeStableMapExt
