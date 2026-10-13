/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.Prespectrum.TelescopeStableEquivalence
import Quillen.Waldhausen.SConstruction.Iterated.Separation

/-!
# Original signed stable-group consumers of telescope invariance

Negative-degree classes and vanishing are witnessed in the actual original
stable groups and through actual finite transitions. An original stable
equivalence, with no levelwise weak-equivalence assumption, induces a stable
equivalence on its two constant-diagram telescopes.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum

namespace QuillenTest.TelescopeStableEquivalence

open Quillen

universe u
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  [∀ i k, T1Space ((E i).space k)]

/-- A negative stable class in the actual telescope is represented in an original stage. -/
theorem original_negative_representative (n : ℕ)
    (a : stableHomotopyGroup (Telescope.prespectrum E f) (-(n : ℤ) - 1)) :
    ∃ i : ℕ, ∃ b : stableHomotopyGroup (E i) (-(n : ℤ) - 1),
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.inclusion E f i) b = a :=
  Telescope.exists_stable_representative E f _ a

/-- Vanishing in a negative stable telescope group is detected by an original finite transition. -/
theorem eventual_original_negative_zero (n i : ℕ)
    (a : stableHomotopyGroup (E i) (-(n : ℤ) - 1))
    (ha : (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.inclusion E f i) a = 0) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.transition E f i N hi) a = 0 := by
  have ha' :
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.inclusion E f i) a =
      (stableHomotopyFunctor (-(n : ℤ) - 1)).map (Telescope.inclusion E f 0) 0 := by
    simpa only [map_zero] using ha
  obtain ⟨N, hi, h0, hN⟩ := Telescope.exists_eventual_stable_eq E f _ a 0 ha'
  exact ⟨N, hi, hN.trans (((stableHomotopyFunctor (-(n : ℤ) - 1)).map
    (Telescope.transition E f 0 N h0)).hom.map_zero)⟩

/-- Constant-diagram telescopes preserve a stable equivalence without a levelwise equivalence. -/
theorem original_constant_telescope_stable_equivalence {A B : LoopPrespectrum.{u}}
    [∀ k, T1Space (A.space k)] [∀ k, T1Space (B.space k)] (g : A ⟶ B)
    (hg : IsStableEquivalence g) :
    IsStableEquivalence
      (Telescope.map (fun _ ↦ A) (fun _ ↦ 𝟙 A) (fun _ ↦ B) (fun _ ↦ 𝟙 B)
        (fun _ ↦ g) (by intro _i; simp)) :=
  Telescope.map_isStableEquivalence _ _ _ _ _ _ (fun _ ↦ hg)

/-- The actual S-prespectrum stages discharge separation in every signed stable degree. -/
theorem iteratedS_signed_representative (W : ℕ → Waldhausen.IteratedS.Model.{u})
    (F : ∀ i, W i ⟶ W (i + 1)) (d : ℤ)
    (a : stableHomotopyGroup
      (Telescope.prespectrum (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
        (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i))) d) :
    ∃ i : ℕ, ∃ b : stableHomotopyGroup (Waldhausen.IteratedS.prespectrum (W i)) d,
      (stableHomotopyFunctor d).map
        (Telescope.inclusion (fun i ↦ Waldhausen.IteratedS.prespectrum (W i))
          (fun i ↦ Waldhausen.IteratedS.prespectrumMap (F i)) i) b = a :=
  Telescope.exists_stable_representative _ _ d a

end QuillenTest.TelescopeStableEquivalence
