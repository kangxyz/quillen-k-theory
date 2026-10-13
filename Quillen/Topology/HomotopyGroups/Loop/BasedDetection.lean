/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.Loop.ComponentTranslation

/-!
# Detecting complete weakness of an original based loop map

Bijectivity in every finite degree at the constant loop detects complete weakness of the actual
based loop map. The natural component translations retain arbitrary source loops, and degree
zero supplies actual target-component coverage. No connectedness hypothesis is imposed.
-/

@[expose] public section

noncomputable section

universe u

namespace Quillen

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- All finite homotopy tests at the constant loop detect the unchanged loop map on every
component, including actual target-component coverage. -/
theorem basedLoopMap_isWeakHomotopyEquivalence_iff_refl (f : C(X, Y)) (h : f x = y) :
    IsWeakHomotopyEquivalence (basedLoopMap f h) ↔
      ∀ n : ℕ, Function.Bijective (homotopyGroupMap (N := Fin n)
        (basedLoopMap f h) (basedLoopMap_refl f h)) := by
  constructor
  · intro hf n
    exact (basedLoopMap_homotopy_bijective_iff_refl f h (Path.refl x) n).mp
      (hf.homotopy_bijective (Path.refl x) n)
  · intro hf
    apply isWeakHomotopyEquivalence_of_point (basedLoopMap f h) (Path.refl x)
    intro γ n
    exact (basedLoopMap_homotopy_bijective_iff_refl f h γ n).mpr (hf n)

/-- Positive-degree bijections at the supplied original point suffice for complete weakness
of the original based loop map, with the genuine loop-degree shift retained. -/
theorem basedLoopMap_isWeakHomotopyEquivalence_of_bijective (f : C(X, Y)) (h : f x = y)
    (hf : ∀ n : ℕ, Function.Bijective (homotopyGroupMap (N := Fin (n + 1)) f h)) :
    IsWeakHomotopyEquivalence (basedLoopMap f h) := by
  apply (basedLoopMap_isWeakHomotopyEquivalence_iff_refl f h).mpr
  intro n
  have he : loopShiftEquiv n ∘ homotopyGroupMap f h =
      homotopyGroupMap (basedLoopMap f h) (basedLoopMap_refl f h) ∘ loopShiftEquiv n :=
    funext (loopShiftEquiv_natural n f h)
  have hb := (loopShiftEquiv (x := y) n).bijective.comp (hf n)
  rw [he] at hb
  exact (Function.Bijective.of_comp_iff _ (loopShiftEquiv (x := x) n).bijective).mp hb

end Quillen
