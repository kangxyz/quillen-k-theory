/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeHomotopyMapStable

/-!
# Track-sensitive consumers of homotopy-compatible telescope maps

The midpoint of an original source cylinder reaches the original target
transition, and three-quarter time samples the supplied transition homotopy
at its midpoint. Arbitrary identity self-tracks still induce actual stable
equivalences. None of these consumers assumes a strict transition square.
-/

open CategoryTheory
open scoped unitInterval
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeHomotopyMap

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i)
  (H : ∀ i, Homotopy (a i ≫ f' i) (f i ≫ a (i + 1)))

/-- The original cylinder midpoint is the original target-transition endpoint. -/
theorem original_midpoint (k i : ℕ) (x : (E i).space k) :
    (Telescope.mapOfHomotopies E f E' f' a H).map k
        (Telescope.cylinder E f k i (⟨1 / 2, by constructor <;> norm_num⟩, x)) =
      (Telescope.inclusion E' f' (i + 1)).map k ((f' i).map k ((a i).map k x)) := by
  have h := Telescope.mapOfHomotopies_first_half E f E' f' a H k i
    ⟨1 / 2, by constructor <;> norm_num⟩ (by norm_num) x
  have ht : (⟨2 * (1 / 2), by norm_num⟩ : unitInterval) = 1 := by ext; norm_num
  simp only [ht] at h
  exact h.trans (Telescope.cylinder_one E' f' k i ((a i).map k x))

/-- Three-quarter cylinder time records the actual supplied homotopy at half time. -/
theorem supplied_track_midpoint (k i : ℕ) (x : (E i).space k) :
    (Telescope.mapOfHomotopies E f E' f' a H).map k
        (Telescope.cylinder E f k i (⟨3 / 4, by constructor <;> norm_num⟩, x)) =
      (Telescope.inclusion E' f' (i + 1)).map k
        ((H i).level k (⟨1 / 2, by constructor <;> norm_num⟩, x)) := by
  have h := Telescope.mapOfHomotopies_second_half E f E' f' a H k i
    ⟨3 / 4, by constructor <;> norm_num⟩ (by norm_num) x
  have ht : (⟨2 * (3 / 4) - 1, by constructor <;> norm_num⟩ : unitInterval) =
      ⟨1 / 2, by constructor <;> norm_num⟩ := by ext; norm_num
  simpa only [ht] using h

/-- Original stage inclusions agree on every signed stable group for the actual map with tracks. -/
theorem original_stage_stable_map (d : ℤ) (i : ℕ) (x : stableHomotopyGroup (E i) d) :
    (stableHomotopyFunctor d).map (Telescope.mapOfHomotopies E f E' f' a H)
        ((stableHomotopyFunctor d).map (Telescope.inclusion E f i) x) =
      (stableHomotopyFunctor d).map (Telescope.inclusion E' f' i)
        ((stableHomotopyFunctor d).map (a i) x) := by
  have h := congrArg ((stableHomotopyFunctor d).map)
    (Telescope.inclusion_mapOfHomotopies E f E' f' a H i)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

/-- Arbitrary original identity self-tracks give a genuine telescope stable equivalence. -/
theorem identity_self_tracks (G : LoopPrespectrum.{u}) [∀ k, T1Space (G.space k)]
    (K : ∀ _i : ℕ, Homotopy (𝟙 G ≫ 𝟙 G) (𝟙 G ≫ 𝟙 G)) :
    IsStableEquivalence
      (Telescope.mapOfHomotopies (fun _ ↦ G) (fun _ ↦ 𝟙 G)
        (fun _ ↦ G) (fun _ ↦ 𝟙 G) (fun _ ↦ 𝟙 G) K) :=
  Telescope.mapOfHomotopies_isStableEquivalence _ _ _ _ _ _
    (fun _ ↦ IsStableEquivalence.id G)

end QuillenTest.TelescopeHomotopyMap
