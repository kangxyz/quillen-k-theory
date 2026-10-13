/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeStableExactness

/-!
# Original-map consumers of telescope stable exactness

A kernel class for the actual homotopy-compatible telescope map lifts from one
original source stage. The actual composite vanishes on every signed stable
group under the explicit stagewise exactness hypothesis.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeStableExactness

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
  (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
  (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
  (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1)))
  (K : ∀ i, Homotopy (b i ≫ h i) (g i ≫ b (i + 1)))
  [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((F i).space k)]
  [∀ i k, T1Space ((G i).space k)]

include f H in
/-- A telescope kernel class has a lift from an actual finite source stage. -/
theorem finite_stage_kernel_lift (d : ℤ)
    (hex : ∀ i, Function.Exact ((stableHomotopyFunctor d).map (a i))
      ((stableHomotopyFunctor d).map (b i)))
    (x : stableHomotopyGroup (Telescope.prespectrum F g) d)
    (hx : (stableHomotopyFunctor d).map (Telescope.mapOfHomotopies F g G h b K) x = 0) :
    ∃ i : ℕ, ∃ y : stableHomotopyGroup (E i) d,
      (stableHomotopyFunctor d).map (Telescope.inclusion F g i)
        ((stableHomotopyFunctor d).map (a i) y) = x := by
  obtain ⟨z, hz⟩ :=
    (Telescope.mapOfHomotopies_stable_exact E f F g G h a b H K d hex x).mp hx
  obtain ⟨i, y, rfl⟩ := Telescope.exists_stable_representative E f d z
  refine ⟨i, y, ?_⟩
  have hi := congrArg ((stableHomotopyFunctor d).map)
    (Telescope.inclusion_mapOfHomotopies E f F g a H i)
  simp only [Functor.map_comp] at hi
  exact (ConcreteCategory.congr_hom hi y).symm.trans hz

/-- The actual telescope composite induces zero in every specified signed degree. -/
theorem original_composite_vanishes (d : ℤ)
    (hex : ∀ i, Function.Exact ((stableHomotopyFunctor d).map (a i))
      ((stableHomotopyFunctor d).map (b i)))
    (x : stableHomotopyGroup (Telescope.prespectrum E f) d) :
    (stableHomotopyFunctor d).map
      (Telescope.mapOfHomotopies E f F g a H ≫ Telescope.mapOfHomotopies F g G h b K) x = 0 := by
  rw [Functor.map_comp]
  exact (Telescope.mapOfHomotopies_stable_exact E f F g G h a b H K d hex _).mpr ⟨x, rfl⟩

end QuillenTest.TelescopeStableExactness
