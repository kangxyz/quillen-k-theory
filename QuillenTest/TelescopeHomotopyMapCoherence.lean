/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeHomotopyMapComposition
import Quillen.Topology.Prespectrum.TelescopeHomotopyMapIdentity

/-!
# Consumers of actual identity and composition telescope homotopies

The actual canonical identity map is homotopic to the original identity without
T1 assumptions. The actual composite and its canonical track-defined map agree
on original level homotopy groups, including degree zero, through a supplied
whole prespectrum homotopy. The canonical transition's second half retains the
first supplied transition track after the original next-stage map.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeHomotopyMapCoherence

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The canonical identity-track telescope map has an actual based homotopy to identity. -/
theorem original_identity_homotopic :
    Nonempty (Homotopy
      (Telescope.mapOfHomotopies E f E f (fun i ↦ 𝟙 (E i))
        (Telescope.identityTransitionHomotopy E f))
      (𝟙 (Telescope.prespectrum E f))) :=
  ⟨Telescope.mapOfHomotopiesIdHomotopy E f⟩

variable (F : ℕ → LoopPrespectrum.{u}) (g : ∀ i, F i ⟶ F (i + 1))
  (G : ℕ → LoopPrespectrum.{u}) (h : ∀ i, G i ⟶ G (i + 1))
  (a : ∀ i, E i ⟶ F i) (b : ∀ i, F i ⟶ G i)
  (H : ∀ i, Homotopy (a i ≫ g i) (f i ≫ a (i + 1)))
  (K : ∀ i, Homotopy (b i ≫ h i) (g i ≫ b (i + 1)))

/-- Actual composition coherence retains every original homotopy group, including π₀. -/
theorem original_composite_homotopyGroupMap (n k : ℕ) :
    homotopyGroupMap (N := Fin k)
        ((Telescope.mapOfHomotopies E f F g a H ≫ Telescope.mapOfHomotopies F g G h b K).map n)
        ((Telescope.mapOfHomotopies E f F g a H ≫
          Telescope.mapOfHomotopies F g G h b K).map_point n) =
      homotopyGroupMap
        ((Telescope.mapOfHomotopies E f G h (fun i ↦ a i ≫ b i)
          (Telescope.composeTransitionHomotopy E f F g G h a b H K)).map n)
        ((Telescope.mapOfHomotopies E f G h (fun i ↦ a i ≫ b i)
          (Telescope.composeTransitionHomotopy E f F g G h a b H K)).map_point n) :=
  (Telescope.mapOfHomotopiesCompHomotopy E f F g G h a b H K).homotopyGroupMap_eq n k

/-- The composite transition at three-quarter time retains the first transition's midpoint. -/
theorem composite_transition_midpoint (n i : ℕ) (x : (E i).space n) :
    (Telescope.composeTransitionHomotopy E f F g G h a b H K i).level n
        (⟨3 / 4, by constructor <;> norm_num⟩, x) =
      (b (i + 1)).map n ((H i).level n (⟨1 / 2, by constructor <;> norm_num⟩, x)) := by
  have ht := ContinuousMap.HomotopyRel.trans_apply
    ((Homotopy.precomp (a i) (K i)).levelHomotopy n)
    ((((H i).postcomp (b (i + 1))).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _)).levelHomotopy n)
    (⟨3 / 4, by constructor <;> norm_num⟩, x)
  have hs : ¬((⟨3 / 4, by constructor <;> norm_num⟩ : unitInterval) : ℝ) ≤ 1 / 2 := by norm_num
  have he : (⟨2 * (3 / 4) - 1, by constructor <;> norm_num⟩ : unitInterval) =
      ⟨1 / 2, by constructor <;> norm_num⟩ := by ext; norm_num
  exact ht.trans ((dite_eq_right hs).trans (by simp only [he]; rfl))

end QuillenTest.TelescopeHomotopyMapCoherence
